from pathlib import Path
from datetime import datetime, timezone
import json,hashlib
A=Path(__file__).resolve().parent
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
F=json.loads((A/'checkpoint23_frozen_source_hashes.json').read_text())
checks=[]; embedded=[]
def check(p,h,context):
 p=Path(p)
 if not p.is_absolute():p=A/p
 assert p.is_file(),(context,str(p),'missing')
 if sha(p)!=h:
  # Older individual-audit records use `sha256` for the Lean SOURCE,
  # not the JSON artifact. Check that documented schema against both.
  assert 'audit' in context and p.suffix=='.json',(context,str(p),'hash mismatch')
  obj=json.loads(p.read_text())
  records=obj.get('modules',[obj])
  matched=[r for r in records if r.get('sha256')==h]
  assert len(matched)==1,(context,p,'record mismatch')
  record=matched[0]
  assert F[record['module']]==h,(context,p,'source mismatch')
  embedded.append({'path':str(p),'module':record['module'],'source_sha256':h,'reference_file_sha256':sha(p),'scope':'source-hash reference validation, not a new compiler run'})
 else: checks.append((str(p),h))
def walk(x,context):
 if isinstance(x,dict):
  if 'path' in x and 'sha256' in x:check(x['path'],x['sha256'],context)
  for k,v in x.items():walk(v,context+'/'+k)
 elif isinstance(x,list):
  for i,v in enumerate(x):walk(v,context+'/'+str(i))
counts={}
for label in ['finite','geometry','analytic']:
 d=json.loads((A/f'checkpoint23_{label}_completion_hashes.json').read_text())
 walk(d,label)
 if label=='finite':
  for p,v in d['inputs'].items():check(p,v['sha256'],label)
  assert {n:v['sha256'] for n,v in d['all_frozen_sources'].items()}==F
  assert {n:v['frozen_sha256'] for n,v in d['all_frozen_sources'].items()}==F
  counts[label]=len(d['selected_modules'])
  for n,v in d['selected_modules'].items():assert v['sha256']==F[n]
 elif label=='geometry':
  for p,h in d['source_hashes'].items():check(p,h,label)
  counts[label]=len(d['lean_sources'])
  for n,v in d['lean_sources'].items():assert v['sha256']==F[n]
 else:
  for name,h in d['source_inputs'].items():
   p=A/'source'/name if name.endswith('.txt') else Path('/Users/ssoh/Downloads')/name
   check(p,h,label)
  counts[label]=len(d['modules'])
  for m in d['modules']:assert m['sha256']==F[m['module']]
  sc=d['signature_checks'];check(sc['log_path'],sc['log_sha256'],label)
  assert sc['compiler_exit_code']==0
report={'status':'PASS','utc':datetime.now(timezone.utc).isoformat(),'all427_source_hashes':len(F),'reviewed_module_sets':counts,'checked_artifact_path_hash_records':len(checks),'unique_checked_artifact_paths':len({p for p,h in checks}),'legacy_embedded_source_hash_records':embedded,'index_files':{f'checkpoint23_{x}_completion_hashes.json':sha(A/f'checkpoint23_{x}_completion_hashes.json') for x in ['finite','geometry','analytic']}}
(A/'checkpoint23_review_index_validation.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps({k:v for k,v in report.items() if k!='legacy_embedded_source_hash_records'}))
print('Legacy embedded-source records checked:',len(embedded))
