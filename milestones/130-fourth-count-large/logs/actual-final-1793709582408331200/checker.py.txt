"""Close the actual-snake equality case only after the entire fixed replay passes."""
from pathlib import Path
import hashlib,json,os,re,subprocess,sys,time
H=Path(__file__).resolve().parents[1];R=H.parents[1];P=R/'milestones/129-fourth-count-three'
B=Path('D:/Codex/2026-10-01/it-should-have-a-property-of/work/lean-research/lean-4.19.0-windows/bin')
read=lambda p:json.loads(p.read_text(encoding='utf-8-sig'))
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
progress=read(P/'data/replay-progress.json')
if progress['status']!='PASS_COMPLETE_CNF_REFUTATION':
 print('NOT_STARTED_FULL_REFUTATION_PENDING');sys.exit(0)
assert len(progress['checked_modules'])==progress['total_modules']==221
assert [x['module'] for x in progress['checked_modules']]==progress['ordered_modules']
deps={str(P/'data/proof-plan.json'):sha(P/'data/proof-plan.json')}
for x in progress['checked_modules']:
 m=x['module'];cnf=m=='Recovered129G.LocalWindowCnf.Triple129'
 rp=P/'data'/('independent-core-cnf-audit.json' if cnf else m+'-audit.json');q=read(rp)
 assert sha(rp)==x['receipt_sha256'] and q['exit_code']==0 and not q.get('timeout',False)
 src=P/'lean'/(m.replace('.','/')+'.lean');obj=P/'build-replay'/(m.replace('.','/')+'.olean')
 assert sha(src)==q['source_sha256'] and sha(obj)==q['importable_object_sha256' if cnf else 'olean_sha256']
 log=Path(q['log']);log=log if log.is_absolute() else P/log;assert sha(log)==q['log_sha256']
 snap=log.parent/'source.lean.txt' if cnf else P/q['source_snapshot'];assert sha(snap)==q['source_sha256']
 for n,d in q['dependencies'].items():
  p=Path(n);p=p if p.is_absolute() else R/p;assert sha(p)==d
 deps.update({str(rp):sha(rp),str(src):sha(src),str(obj):sha(obj),str(log):sha(log),str(snap):sha(snap)})
for name,rp in [('CoreSemantics129',P/'data/independent-core-semantics-audit.json'),
                ('ActualSplit129',P/'logs/actual-split-1793689366716282000/record.json')]:
 q=read(rp);assert q['status']=='PASS' and q['exit_code']==0 and not q.get('timeout',False)
 assert sha(P/'lean'/(name+'.lean'))==q['source_sha256']
 for k in ['object','importable_object','log']:assert sha(q[k])==q[k+'_sha256'];deps[q[k]]=q[k+'_sha256']
 deps[str(rp)]=sha(rp)
 for n,d in q['dependencies'].items():assert sha(n)==d;deps[n]=d
environment=R/'milestones/125-critical-six-count/data/environment-sum.json'
paths=[str(H/'build-independent'),str(P/'build-replay'),str(P/'build-independent')]+read(environment)['paths']
deps[str(environment)]=sha(environment)
source=H/'lean/ActualFourthThree130.lean'
for name in re.findall(r'^import ([\w.]+)$',source.read_text(),re.M):
 obj=next(Path(p)/(name.replace('.','/')+'.olean') for p in paths if (Path(p)/(name.replace('.','/')+'.olean')).exists())
 deps[str(obj)]=sha(obj)
resource=json.loads(subprocess.check_output(['powershell','-NoProfile','-Command',"$o=Get-CimInstance Win32_OperatingSystem;$p=@(Get-CimInstance Win32_Process -Filter \"Name='lean.exe'\"|Select-Object ProcessId);@{available_bytes=[long]$o.FreePhysicalMemory*1024;processes=$p}|ConvertTo-Json -Depth 3 -Compress"],text=True))
if resource['available_bytes']<1536*1024**2 or len(resource['processes'])>2:
 print('NOT_STARTED_RESOURCE_GATE');sys.exit(0)
run=str(time.time_ns());attempt=H/'logs'/('actual-final-'+run);attempt.mkdir()
record=attempt/'record.json';obj=H/'build-independent'/('ActualFourthThree130-'+run+'.olean');log=attempt/'compiler.log'
(attempt/'source.lean.txt').write_bytes(source.read_bytes());(attempt/'checker.py.txt').write_bytes(Path(__file__).read_bytes())
state=dict(status='COMPILING',pid=os.getpid(),source_sha256=sha(source),checker_sha256=sha(__file__),
 source=str(source),dependencies=deps,paths=paths,resource=resource,object=str(obj),log=str(log))
def save():record.write_text(json.dumps(state,indent=2)+'\n',encoding='utf-8')
env=os.environ.copy();env['PATH']=str(B)+';'+env['PATH'];env['LEAN_PATH']=';'.join(paths)
start=time.monotonic();save()
with log.open('w',encoding='utf-8') as out:
 proc=subprocess.Popen([str(B/'lake.exe'),'env','lean','-s','65536','-R',str(H/'lean'),'-o',str(obj),str(source)],cwd=B.parent.parent/'mathlib',env=env,stdout=out,stderr=subprocess.STDOUT)
 state['launcher_pid']=proc.pid;save()
 try:code=proc.wait(timeout=600)
 except subprocess.TimeoutExpired:
  subprocess.run(['taskkill','/PID',str(proc.pid),'/T','/F'],stdout=subprocess.DEVNULL,stderr=subprocess.DEVNULL);code=proc.wait();state['timeout']=True
state.update(exit_code=code,seconds=time.monotonic()-start,log_sha256=sha(log))
text=log.read_text();rows=re.findall(r"'([^']+)' depends on axioms:\s*\[([^]]*)\]",text,re.S)
state['axioms']=[dict(theorem=n,axioms=re.findall(r'[A-Za-z][\w.]*',a)) for n,a in rows]
ok=code==0 and not state.get('timeout') and 'error:' not in text and 'sorryAx' not in text and len(rows)==3
ok=ok and sha(source)==state['source_sha256'] and sha(__file__)==state['checker_sha256'] and all(sha(n)==d for n,d in deps.items())
ok=ok and all(set(x['axioms'])<={'propext','Classical.choice','Quot.sound'} for x in state['axioms'])
ok=ok and not re.search(r'\b(sorry|admit|native_decide|axiom)\b',source.read_text())
state['status']='PASS' if ok else 'FAILED'
if obj.exists():state['object_sha256']=sha(obj)
if ok:
 stable=H/'build-independent/ActualFourthThree130.olean';stable.write_bytes(obj.read_bytes())
 state.update(importable_object=str(stable),importable_object_sha256=sha(stable),scope='Actual triple floor12 and six-count floor23 when fourth count3; total22 therefore forces fourth>=4. No global bound.')
save()
if ok:(H/'data/independent-actual-final-audit.json').write_bytes(record.read_bytes())
print(json.dumps(dict(status=state['status'],seconds=state['seconds'],axioms=state['axioms'],record=str(record))))
sys.exit(0 if ok else 1)
