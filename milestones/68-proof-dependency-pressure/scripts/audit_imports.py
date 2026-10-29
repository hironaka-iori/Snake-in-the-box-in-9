from pathlib import Path
import hashlib,json,re
HERE=Path(__file__).resolve().parents[1];ROOT=HERE.parents[1]
rows=[]
for milestone in ['51-exact-bucket-pressure','52-share-on-235','53-shares-on-sat-obstruction','54-share-coverage']:
 folder=ROOT/f'milestones/{milestone}';p=folder/'data/verification.json';r=json.loads(p.read_text());assert r['status']=='PASS'
 sources=r.get('source_hashes',{});checked=0
 for name,digest in sources.items():
  src=folder/'lean'/(name+'.lean');assert hashlib.sha256(src.read_bytes()).hexdigest()==digest;checked+=1
 names=['ReverseShareRule'] if milestone.startswith('54') else ['ShareInSnake0','ShareInSnake5'] if milestone.startswith('53') else ['ShareInSnake']
 audits=[]
 for name in names:
  log=folder/f'logs/{name}.log';txt=log.read_text(encoding='utf-8');assert 'error:' not in txt and 'sorryAx' not in txt
  entries=re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]",txt,re.S);assert entries
  assert all(set(re.findall(r'[A-Za-z][\w.]*',a))<={'propext','Classical.choice','Quot.sound'} for _,a in entries)
  audits.extend(n for n,a in entries)
 rows.append(dict(milestone=milestone,receipt=str(p.relative_to(ROOT)),receipt_sha256=hashlib.sha256(p.read_bytes()).hexdigest(),source_hashes_rechecked=checked,selected_logged_theorems=audits))
out=dict(status='PASS',records=rows,scope='Rechecks saved proof receipts, matching current source hashes where recorded, and standard-axiom logs for four inherited share rules and their reversal. This is an audit of prior runs, not a fresh rebuild.')
(HERE/'data/import-audit.json').write_text(json.dumps(out,indent=2)+'\n');print(out)
