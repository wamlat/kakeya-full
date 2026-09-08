#!/usr/bin/env python3
"""Build all delivered modules and audit every local theorem via Lean's environment.

Run after `lake update`, or reuse a matching installed Mathlib checkout with
--mathlib-project /absolute/path. Sources and generated audits compile in a
separate scratch project; the supplied dependency project's sources are untouched.
"""
import argparse
from concurrent.futures import ThreadPoolExecutor
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import re
import shutil
import subprocess

ROOT = Path(__file__).resolve().parent
TRUSTED = {'propext', 'Classical.choice', 'Quot.sound'}
AUDIT = '''
run_cmd do
  let env ← Lean.getEnv
  for (name, info) in env.constants.toList do
    if (env.getModuleIdxFor? name).isNone && info.isTheorem then
      let axioms ← Lean.collectAxioms name
      Lean.logInfo m!"AUDIT_THEOREM {name} AXIOMS {axioms}"
    if (env.getModuleIdxFor? name).isNone && !info.isTheorem then
      let axioms ← Lean.collectAxioms name
      Lean.logInfo m!"AUDIT_DECLARATION {name} AXIOMS {axioms}"
    if (env.getModuleIdxFor? name).isNone then
      match info with
      | .axiomInfo _ => Lean.logInfo m!"AUDIT_AXIOM {name}"
      | _ => pure ()
'''


def without_comments(text):
    result=[]; depth=0; i=0
    while i<len(text):
        if text[i:i+2]=='/-': depth+=1; i+=2
        elif depth and text[i:i+2]=='-/': depth-=1; i+=2
        elif depth: i+=1
        elif text[i:i+2]=='--':
            end=text.find('\n',i); i=len(text) if end<0 else end
        else: result.append(text[i]); i+=1
    if depth: raise ValueError('Unclosed block comment')
    return ''.join(result)


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--mathlib-project',type=Path,default=ROOT)
    parser.add_argument('--scratch',type=Path,default=ROOT/'verification-work')
    parser.add_argument('--log-dir',type=Path,default=ROOT/'verification')
    parser.add_argument('--lake',default=shutil.which('lake') or str(Path.home()/'.elan/bin/lake'))
    parser.add_argument('--workers',type=int,default=3)
    parser.add_argument('--reject-external-axioms',action='store_true',
                        help='Require standard foundations only, even if an external registry exists')
    args=parser.parse_args()
    deps=args.mathlib_project.resolve(); scratch=args.scratch.resolve(); logs=args.log_dir.resolve()
    scratch.mkdir(parents=True,exist_ok=True); logs.mkdir(parents=True,exist_ok=True)
    modules=re.findall(r'(?m)^@\[default_target\] lean_lib (\w+)\s*$',(ROOT/'lakefile.lean').read_text())
    if not modules: raise RuntimeError('No delivered libraries listed')
    registry_path=ROOT/'external_axioms.json'
    registry=json.loads(registry_path.read_text()) if registry_path.exists() else {'axioms':[]}
    external={a['name']:a for a in registry['axioms']}
    if len(external)!=len(registry['axioms']): raise RuntimeError('Duplicate external axiom registration')
    if args.reject_external_axioms and external: raise RuntimeError('External axioms rejected by strict verification mode')
    for name,item in external.items():
        for field in ['module','source_url','source_locator','formal_statement','trust_boundary','module_sha256']:
            if not item.get(field): raise RuntimeError(f'{name}: missing registry field {field}')
        if item['module'] not in modules: raise RuntimeError(f'{name}: unregistered source module')
        source=ROOT/(item['module']+'.lean')
        if hashlib.sha256(source.read_bytes()).hexdigest()!=item['module_sha256']:
            raise RuntimeError(f'{name}: external source differs from reviewed registry hash')
    manifest=json.loads((deps/'lake-manifest.json').read_text())
    mathlib=next(p for p in manifest['packages'] if p['name']=='mathlib')
    pinned=re.search(r'@\s*"([0-9a-f]{40})"',(ROOT/'lakefile.lean').read_text()).group(1)
    if mathlib['rev'] != pinned: raise RuntimeError('Supplied Mathlib revision differs from pinned revision')
    dep_packages=deps/'.lake/packages'
    if not dep_packages.is_dir(): raise RuntimeError('Missing packages: first run lake update or pass --mathlib-project')
    (scratch/'.lake').mkdir(exist_ok=True)
    link=scratch/'.lake/packages'
    if not link.exists(): link.symlink_to(dep_packages.resolve(),target_is_directory=True)
    elif link.resolve()!=dep_packages.resolve(): raise RuntimeError('Scratch directory uses different dependencies')
    for f in ['lakefile.lean','lean-toolchain','lake-manifest.json','exact_checks.py','verify.py']+[m+'.lean' for m in modules]:
        shutil.copy2(ROOT/f,scratch/f)
    if registry_path.exists(): shutil.copy2(registry_path,scratch/'external_axioms.json')
    version=subprocess.run([args.lake,'env','lean','--version'],cwd=scratch,capture_output=True,text=True,check=True).stdout.strip()
    build=subprocess.run([args.lake,'build'],cwd=scratch,capture_output=True,text=True)
    (logs/'lake-build.log').write_text(build.stdout+build.stderr)
    if build.returncode: raise RuntimeError('Package build failed; see lake-build.log')

    def compile_module(module):
        source=scratch/f'{module}.lean'; source_text=source.read_text(); code=without_comments(source_text)
        forbidden=re.findall(r'\b(?:sorry|admit|native_decide|unsafe)\b',code)
        if forbidden: raise RuntimeError(f'{module}: forbidden proof construct {forbidden}')
        source_names=re.findall(r'(?m)^(?:@\[[^\n]*\]\s*)?(?:(?:private|protected|noncomputable)\s+)*(?:theorem|lemma)\s+([\w\u0080-\uffff\x27.]+)',code)
        generated=scratch/f'{module}_AxiomAudit.lean'; generated.write_text(source_text+'\n'+AUDIT)
        command=[args.lake,'env','lean',str(generated)]
        proc=subprocess.run(command,cwd=scratch,capture_output=True,text=True)
        output=proc.stdout+proc.stderr; (logs/f'{module}.log').write_text(output)
        if proc.returncode: raise RuntimeError(f'{module}: compiler failed; see log')
        if re.search(r'\b(?:warning|error)(?:\([^)]*\))?:',output): raise RuntimeError(f'{module}: compiler diagnostic; see log')
        reports=re.findall(r'AUDIT_THEOREM (\S+) AXIOMS \[([^]]*)\]',output)
        declaration_reports=re.findall(r'AUDIT_DECLARATION (\S+) AXIOMS \[([^]]*)\]',output)
        if not reports: raise RuntimeError(f'{module}: no theorem inventory')
        declared=sorted(re.findall(r'(?m)^.*?AUDIT_AXIOM (\S+)\s*$',output))
        expected=sorted(name for name,item in external.items() if item['module']==module)
        if declared!=expected: raise RuntimeError(f'{module}: declared axioms {declared}, expected {expected}')
        source_axioms=re.findall(r'(?m)^axiom\s+(\S+)',code)
        if len(source_axioms)!=len(declared): raise RuntimeError(f'{module}: source/environment axiom mismatch')
        axioms={a.strip() for _,block in reports+declaration_reports for a in block.split(',') if a.strip()}
        if axioms-TRUSTED-external.keys(): raise RuntimeError(f'{module}: unexpected axioms {axioms-TRUSTED-external.keys()}')
        dependencies={name:sorted(a.strip() for a in block.split(',') if a.strip()) for name,block in reports}
        declaration_dependencies={name:sorted(a.strip() for a in block.split(',') if a.strip())
                                  for name,block in reports+declaration_reports}
        external_dependencies={name:sorted(set(deps)&external.keys()) for name,deps in dependencies.items()
                               if set(deps)&external.keys()}
        external_declaration_dependencies={name:sorted(set(deps)&external.keys())
                                           for name,deps in declaration_dependencies.items()
                                           if set(deps)&external.keys()}
        names=sorted(n for n,_ in reports)
        for n in source_names:
            if not any(full==n or full.endswith('.'+n) for full in names):
                raise RuntimeError(f'{module}: source declaration {n} missing from environment audit')
        return {'module':module,'theorem_count':len(source_names),'source_declarations':source_names,
                'audited_theorem_count':len(names),'audited_theorems':names,
                'source_sha256':hashlib.sha256(source.read_bytes()).hexdigest(),
                'compiler_exit_code':proc.returncode,'axioms':sorted(axioms),'command':command,
                'declared_external_axioms':declared,'theorem_dependencies':dependencies,
                'theorems_using_external_axioms':external_dependencies,
                'audited_declaration_count':len(declaration_dependencies),
                'declaration_dependencies':declaration_dependencies,
                'declarations_using_external_axioms':external_declaration_dependencies}
    with ThreadPoolExecutor(max_workers=args.workers) as pool:
        results=list(pool.map(compile_module,modules))
    exact=subprocess.run([shutil.which('python3') or 'python3',str(scratch/'exact_checks.py')],cwd=scratch,capture_output=True,text=True,check=True)
    (logs/'exact_checks.json').write_text(exact.stdout)
    summary={'status':'PASS','utc':datetime.now(timezone.utc).isoformat(),'lean_version':version,
             'mathlib_revision':mathlib['rev'],'theorem_count':sum(r['theorem_count'] for r in results),
             'audited_theorem_count':sum(r['audited_theorem_count'] for r in results),'modules':results,
             'audited_declaration_count':sum(r['audited_declaration_count'] for r in results),
             'trust_mode':'registered_published_axioms' if external else 'standard_foundations_only',
             'external_axioms':list(external.values()),
             'theorems_using_external_axioms':sum(len(r['theorems_using_external_axioms']) for r in results),
             'declarations_using_external_axioms':sum(len(r['declarations_using_external_axioms']) for r in results),
             'exact_named_checks':json.loads(exact.stdout)['named_checks'],
             'scope':'All local declarations in every delivered module, including definitions, proof-bearing data and generated declarations, were audited for logical dependencies. This verifies the delivered formal statements and their recorded assumptions; correspondence with the manuscript and coverage of its results require the separate source completion audit.'}
    (logs/'summary.json').write_text(json.dumps(summary,indent=2)+'\n')
    print(json.dumps({k:summary[k] for k in ('status','theorem_count','audited_theorem_count','exact_named_checks','trust_mode','theorems_using_external_axioms','lean_version','mathlib_revision','scope')},indent=2))

if __name__=='__main__': main()
