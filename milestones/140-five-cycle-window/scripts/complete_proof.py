"""Complete the actual-window proof after the live120-module replay; never restart it."""
from pathlib import Path
import datetime,hashlib,json,re,subprocess,sys
H=Path(__file__).resolve().parents[1];R=H.parents[1]
read=lambda p:json.loads(Path(p).read_text(encoding='utf-8-sig'))
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
plan=read(H/'data/proof-plan-base.json');final=H/'data/proof-completion.json'
assert not final.exists(),'Preserve the existing proof completion'
receipts=[]
for name in plan['module_order']:
 if name==plan['final_module']:continue
 path=H/'data'/(name+'-audit.json')
 if not path.exists():
  print(json.dumps(dict(status='NOT_READY_REPLAY_INCOMPLETE',missing=name)));sys.exit(0)
 q=read(path);assert q['status']=='PASS_WINDOW_REPLAY_MODULE' and q['exit_code']==0 and not q['timeout']
 source=H/'lean'/(name.replace('.','/')+'.lean')
 assert sha(source)==q['source_sha256']==sha(H/q['source_snapshot'])
 assert sha(H/q['log'])==q['log_sha256']
 assert sha(H/'build-base'/(name.replace('.','/')+'.olean'))==q['olean_sha256']
 for p,d in q['dependencies'].items():assert sha(Path(p) if Path(p).is_absolute() else R/p)==d,p
 assert all(set(a['axioms'])<={'propext','Classical.choice','Quot.sound'} for a in q['theorem_audits'])
 receipts.append(dict(module=name,path=path.relative_to(R).as_posix(),sha256=sha(path)))
assert len(receipts)==120
reports=[]
for name in ['Weak140Semantics','ActualBase140','Weak140Actual']:
 path=H/'data'/(name+'-audit.json')
 if not path.exists():
  code=subprocess.run([sys.executable,'-B','-X','utf8',str(H/'scripts/check_module.py'),name],cwd=R).returncode
  assert code==0,(name,code)
  if not path.exists():
   print(json.dumps(dict(status='NOT_STARTED_RESOURCE_GATE',module=name)));sys.exit(0)
 q=read(path);assert q['status']=='PASS' and q['exit_code']==0 and not q.get('timeout',False)
 source=H/'lean'/(name+'.lean');assert sha(source)==q['source_sha256']
 for key in ['object','importable_object','log']:assert sha(q[key])==q[key+'_sha256']
 for p,d in q['dependencies'].items():assert sha(Path(p) if Path(p).is_absolute() else R/p)==d,p
 assert all(set(a['axioms'])<={'propext','Classical.choice','Quot.sound'} for a in q['axioms'])
 assert len(q['axioms'])=={'Weak140Semantics':2,'ActualBase140':4,'Weak140Actual':5}[name]
 reports.extend(q['axioms']);receipts.append(dict(module=name,path=path.relative_to(R).as_posix(),sha256=sha(path)))
assert any(a['theorem']=='Snake9.Weak140.actual_one_count_ge_six' for a in reports)
src=H/'lean/Weak140Actual.lean';receipt=H/'data/Weak140Actual-audit.json'
completion=dict(status='PASS_ACTUAL_012032_WEAK_EXCLUSION',recorded_at=datetime.datetime.now(datetime.timezone.utc).isoformat(),
 modules=123,receipts=receipts,actual_and_weak_axiom_reports=reports,
 weak_actual_theorem=dict(checked=True,directions=[0,1,2,0,3,2],bounds=[[3,3],[0,5],[4,4],[0,5],[3,3]],
 theorem='Snake9.Weak140.actual_weak_counts',consequence='Snake9.Weak140.actual_one_count_ge_six',source=src.relative_to(R).as_posix(),source_sha256=sha(src),receipt=receipt.relative_to(R).as_posix(),receipt_sha256=sha(receipt)),
 plan_sha256=sha(H/'data/proof-plan-base.json'),native_record_sha256=sha(H/'data/native-base.json'),checker_sha256=sha(Path(__file__)),
 scope='Actual fitting canonical012032 windows in either parity: counts1,3,5 equal3,4,3 force count2>=6 or count4>=6. No endpoint-location restriction. No new global length bound or finite graph minimum is asserted.')
final.write_text(json.dumps(completion,indent=2)+'\n',encoding='utf-8');print(json.dumps({k:v for k,v in completion.items() if k not in ['receipts','actual_and_weak_axiom_reports']}))
