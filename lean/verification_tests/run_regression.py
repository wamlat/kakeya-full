#!/usr/bin/env python3
"""Run 12 portable, synthetic regression tests of a delivered Lean verifier.

Every fixture builds a small real Lean library. No full package build is run.
The synthetic registry and zero-check arithmetic stub test verifier behavior;
they do not assert any Kakeya result or replace the package's mathematical tests.
"""
import argparse
from concurrent.futures import ThreadPoolExecutor
from dataclasses import dataclass
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import re
import shutil
import subprocess
import sys
import tempfile


@dataclass(frozen=True)
class Case:
    name: str
    body: str
    accepted: bool
    registered: bool = False
    bad_hash: bool = False
    strict: bool = False
    rejection: str = ''


STANDARD = 'theorem checked : True := True.intro\n'
REGISTERED = 'axiom published : True\ntheorem usesPublished : True := published\n'
CERTIFICATE = '''set_option linter.deprecated false
structure Certificate : Type where
  proof : True
def proofCertificate : Certificate := ⟨Lean.trustCompiler⟩
theorem unrelated : True := True.intro
'''
REGISTERED_CERTIFICATE = '''structure Certificate : Type where
  proof : True
axiom published : True
def proofCertificate : Certificate := ⟨published⟩
theorem unrelated : True := True.intro
'''
CASES = [
    Case('standard_pass', STANDARD, True),
    Case('registered_pass', REGISTERED, True, registered=True),
    Case('unregistered_axiom', 'axiom rogue : True\ntheorem usesRogue : True := rogue\n',
         False, rejection="declared axioms ['Fixture.rogue']"),
    Case('unregistered_dependency', 'set_option linter.deprecated false\n'
         'theorem usesCompilerAxiom : True := Lean.trustCompiler\n', False,
         rejection="unexpected axioms {'Lean.trustCompiler'}"),
    Case('registry_hash_mismatch', REGISTERED, False, registered=True, bad_hash=True,
         rejection='external source differs from reviewed registry hash'),
    Case('strict_rejects_registered', REGISTERED, False, registered=True, strict=True,
         rejection='External axioms rejected by strict verification mode'),
    Case('strict_accepts_standard', STANDARD, True, strict=True),
    Case('sorry_rejected', 'theorem unfinished : True := by sorry\n', False,
         rejection="forbidden proof construct ['sorry']"),
    Case('native_decide_rejected', 'theorem nativeChecked : (1 : Nat) = 1 := by native_decide\n',
         False, rejection="forbidden proof construct ['native_decide']"),
    Case('data_definition_dependency', CERTIFICATE, False,
         rejection="unexpected axioms {'Lean.trustCompiler'}"),
    Case('opaque_definition_dependency', CERTIFICATE.replace('def proofCertificate',
         'opaque proofCertificate'), False, rejection="unexpected axioms {'Lean.trustCompiler'}"),
    Case('registered_definition', REGISTERED_CERTIFICATE, True, registered=True),
]


def main():
    here = Path(__file__).resolve().parent
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--package', type=Path, default=here.parent,
                        help='Package containing verify.py (default: parent of this test folder)')
    parser.add_argument('--mathlib-project', type=Path,
                        help='Matching existing dependency project (default: --package)')
    parser.add_argument('--lake', default=shutil.which('lake') or str(Path.home()/'.elan/bin/lake'),
                        help='Lake executable or command name')
    parser.add_argument('--work-dir', type=Path, default=Path.cwd()/'verification-test-work',
                        help='Parent for a fresh scratch run and all detailed logs')
    parser.add_argument('--result-json', type=Path, default=here/'results.json',
                        help='Portable summary artifact (default: results.json beside this script)')
    parser.add_argument('--workers', type=int, default=3,
                        help='Number of simultaneous single-module fixtures (default: 3)')
    args = parser.parse_args()
    if args.workers < 1:
        parser.error('--workers must be positive')
    package = args.package.expanduser().resolve()
    deps = (args.mathlib_project or package).expanduser().resolve()
    lake = str(Path(shutil.which(args.lake) or args.lake).expanduser().resolve())
    if not Path(lake).is_file():
        parser.error('Lake executable not found; supply --lake')
    for directory, names in [(package, ['verify.py', 'lakefile.lean', 'lean-toolchain']),
                             (deps, ['lake-manifest.json'])]:
        for name in names:
            if not (directory/name).is_file():
                parser.error(f'Missing {name} in {directory}')
    if not (deps/'.lake/packages').is_dir():
        parser.error('Dependency packages are missing; run lake update or use --mathlib-project')
    verifier = (package/'verify.py').read_bytes()
    verifier_hash = hashlib.sha256(verifier).hexdigest()
    lakefile = (package/'lakefile.lean').read_text()
    pinned_match = re.search(r'@\s*"([0-9a-f]{40})"', lakefile)
    package_match = re.search(r'(?m)^package\s+(\w+)', lakefile)
    if not pinned_match or not package_match:
        parser.error('Cannot read the package name and pinned dependency revision from lakefile.lean')
    pinned = pinned_match.group(1)
    manifest = json.loads((deps/'lake-manifest.json').read_text())
    mathlib = next((p for p in manifest['packages'] if p['name'] == 'mathlib'), None)
    if not mathlib or mathlib['rev'] != pinned:
        parser.error('Dependency project does not match the package Mathlib revision')
    args.work_dir.expanduser().resolve().mkdir(parents=True, exist_ok=True)
    run = Path(tempfile.mkdtemp(prefix='axiom-regression-',
                               dir=args.work_dir.expanduser().resolve()))
    fixture_lakefile = f'''import Lake
open Lake DSL
package {package_match.group(1)}
require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @
  "{pinned}"
@[default_target] lean_lib Fixture
'''

    def run_case(case):
        root = run/case.name
        root.mkdir()
        source = 'import Lean\nnamespace Fixture\n'+case.body+'end Fixture\n'
        (root/'verify.py').write_bytes(verifier)
        (root/'Fixture.lean').write_text(source)
        (root/'lakefile.lean').write_text(fixture_lakefile)
        shutil.copy2(package/'lean-toolchain', root/'lean-toolchain')
        shutil.copy2(deps/'lake-manifest.json', root/'lake-manifest.json')
        (root/'exact_checks.py').write_text('import json\nprint(json.dumps({"named_checks": 0}))\n')
        registry = []
        if case.registered:
            registry = [{
                'name': 'Fixture.published', 'module': 'Fixture',
                'source_url': 'https://example.invalid/synthetic-verifier-test',
                'source_locator': 'Synthetic True axiom; not a published result',
                'formal_statement': 'Fixture.published : True',
                'trust_boundary': 'Verifier regression fixture only; no mathematical import',
                'module_sha256': '0'*64 if case.bad_hash else hashlib.sha256(source.encode()).hexdigest(),
            }]
        (root/'external_axioms.json').write_text(json.dumps({'axioms': registry}, indent=2)+'\n')
        command = [sys.executable, str(root/'verify.py'), '--mathlib-project', str(deps),
                   '--scratch', str(root/'scratch'), '--log-dir', str(root/'logs'),
                   '--lake', lake, '--workers', '1']
        if case.strict:
            command.append('--reject-external-axioms')
        proc = subprocess.run(command, capture_output=True, text=True)
        output = proc.stdout+proc.stderr
        (root/'invocation.log').write_text(output)
        (root/'command.json').write_text(json.dumps(command, indent=2)+'\n')
        problems = []
        if (proc.returncode == 0) != case.accepted:
            problems.append('unexpected acceptance/rejection')
        if case.rejection and case.rejection not in output:
            problems.append('intended rejection reason missing')
        summary_path = root/'logs/summary.json'
        summary = json.loads(summary_path.read_text()) if summary_path.exists() else {}
        module = next(iter(summary.get('modules', [])), {})
        if case.accepted:
            if summary.get('status') != 'PASS':
                problems.append('PASS summary missing')
            expected_mode = 'registered_published_axioms' if case.registered else 'standard_foundations_only'
            if summary.get('trust_mode') != expected_mode:
                problems.append('incorrect trust mode')
            if case.name == 'registered_pass':
                if module.get('theorem_dependencies', {}).get('Fixture.usesPublished') != ['Fixture.published']:
                    problems.append('registered theorem dependency missing')
            if case.name == 'registered_definition':
                if module.get('declaration_dependencies', {}).get('Fixture.proofCertificate') != ['Fixture.published']:
                    problems.append('registered proof-definition dependency missing')
                if 'Fixture.proofCertificate' not in module.get('declarations_using_external_axioms', {}):
                    problems.append('proof-definition external inventory missing')
                if summary.get('theorems_using_external_axioms') != 0:
                    problems.append('proof definition incorrectly counted as an external-dependent theorem')
        row = {
            'case': case.name, 'status': 'FAIL' if problems else 'PASS',
            'expected': 'accept' if case.accepted else 'reject',
            'returncode': proc.returncode, 'problems': problems,
            'verified_rejection': case.rejection or None,
            'fixture_source_sha256': hashlib.sha256(source.encode()).hexdigest(),
            'log_subdirectory': case.name,
        }
        if summary:
            row['inventory'] = {name: summary.get(name) for name in [
                'lean_version', 'trust_mode', 'theorem_count', 'audited_theorem_count',
                'audited_declaration_count', 'theorems_using_external_axioms',
                'declarations_using_external_axioms']}
        if case.name == 'registered_definition' and summary:
            row['proof_record_dependency'] = module.get('declaration_dependencies', {}).get('Fixture.proofCertificate')
        print(f"{row['status']}: {case.name} ({row['expected']}, exit {proc.returncode})", flush=True)
        return row

    with ThreadPoolExecutor(max_workers=args.workers) as pool:
        results = list(pool.map(run_case, CASES))
    unchanged = hashlib.sha256((package/'verify.py').read_bytes()).hexdigest() == verifier_hash
    passed = unchanged and all(row['status'] == 'PASS' for row in results)
    report = {
        'status': 'PASS' if passed else 'FAIL',
        'utc': datetime.now(timezone.utc).isoformat(),
        'scope': 'Synthetic verifier acceptance/rejection tests; no full package rebuild or Kakeya proof claim',
        'case_count': len(results), 'expected_acceptances': sum(case.accepted for case in CASES),
        'expected_rejections': sum(not case.accepted for case in CASES),
        'verifier_sha256': verifier_hash, 'verifier_unchanged_during_run': unchanged,
        'harness_sha256': hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        'lean_toolchain': (package/'lean-toolchain').read_text().strip(),
        'mathlib_revision': pinned, 'work_subdirectory': run.name, 'cases': results,
    }
    result_path = args.result_json.expanduser().resolve()
    result_path.parent.mkdir(parents=True, exist_ok=True)
    result_path.write_text(json.dumps(report, indent=2)+'\n')
    (run/'results.json').write_text(json.dumps(report, indent=2)+'\n')
    print(f"{report['status']}: {len(results)} cases; detailed logs: {run}")
    print(f"Portable result: {result_path}")
    return 0 if passed else 1


if __name__ == '__main__':
    sys.exit(main())
