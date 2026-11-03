"""Check conditional arithmetic without certifying the graph premises."""
from pathlib import Path
import hashlib,json,os,re,subprocess,sys,time
H=Path(__file__).resolve().parents[1]
B=Path('D:/Codex/2026-10-01/it-should-have-a-property-of/work/lean-research/lean-4.19.0-windows/bin')
M=B.parent.parent/'mathlib'
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
resource=json.loads(subprocess.check_output(['powershell','-NoProfile','-Command',
 '$o=Get-CimInstance Win32_OperatingSystem;$p=@(Get-CimInstance Win32_Process -Filter "Name=\'lean.exe\'"|Select-Object ProcessId);@{available_bytes=[long]$o.FreePhysicalMemory*1024;processes=$p}|ConvertTo-Json -Depth 3 -Compress'],text=True))
if resource['available_bytes']<1536*1024**2 or len(resource['processes'])>2:
 print('NOT_STARTED_RESOURCE_GATE');sys.exit(0)
src=H/'lean/CreditLimitation132.lean'
assert not re.search(r'\b(sorry|admit|native_decide|axiom)\b',src.read_text())
deps={str(p):sha(p) for p in [B/'lean.exe',B/'lake.exe',M/'lean-toolchain',M/'lake-manifest.json',
 M/'.lake/build/lib/lean/Mathlib/Tactic.olean']}
run=str(time.time_ns());attempt=H/'logs'/('credit-'+run);attempt.mkdir(parents=True)
build=H/'build-independent';build.mkdir(exist_ok=True)
obj=build/('CreditLimitation132-'+run+'.olean');log=attempt/'compiler.log';record=attempt/'record.json'
(attempt/'source.lean.txt').write_bytes(src.read_bytes());(attempt/'checker.py.txt').write_bytes(Path(__file__).read_bytes())
state=dict(status='COMPILING',pid=os.getpid(),source=str(src),source_sha256=sha(src),checker_sha256=sha(__file__),
 dependencies=deps,resource=resource,object=str(obj),log=str(log),cwd=str(M))
def save():record.write_text(json.dumps(state,indent=2)+'\n',encoding='utf-8')
env=os.environ.copy();env['PATH']=str(B)+';'+env['PATH'];env.pop('LEAN_PATH',None)
command=[str(B/'lake.exe'),'env','lean','-s','65536','-R',str(H/'lean'),'-o',str(obj),str(src)]
state['command']=command;save();start=time.monotonic()
with log.open('w',encoding='utf-8') as out:
 child=subprocess.Popen(command,cwd=M,env=env,stdout=out,stderr=subprocess.STDOUT)
 state['launcher_pid']=child.pid;save()
 try:code=child.wait(timeout=180)
 except subprocess.TimeoutExpired:
  subprocess.run(['taskkill','/PID',str(child.pid),'/T','/F'],stdout=subprocess.DEVNULL,stderr=subprocess.DEVNULL)
  code=child.wait();state['timeout']=True
text=log.read_text();reports=[dict(theorem=n,axioms=re.findall(r'[A-Za-z][\w.]*',a))
 for n,a in re.findall(r"'([^']+)' depends on axioms:\s*\[([^]]*)\]",text,re.S)]
reports.extend(dict(theorem=n,axioms=[]) for n in re.findall(r"'([^']+)' does not depend on any axioms",text))
state.update(exit_code=code,seconds=time.monotonic()-start,log_sha256=sha(log),axioms=reports)
ok=code==0 and not state.get('timeout') and 'error:' not in text and 'sorryAx' not in text
ok=ok and len(reports)==2 and all(set(x['axioms'])<={'propext','Classical.choice','Quot.sound'} for x in reports)
ok=ok and sha(src)==state['source_sha256'] and sha(__file__)==state['checker_sha256'] and all(sha(p)==d for p,d in deps.items())
state['status']='PASS' if ok else 'FAILED'
if obj.exists():state['object_sha256']=sha(obj)
if ok:
 stable=build/'CreditLimitation132.olean';stable.write_bytes(obj.read_bytes())
 state.update(importable_object=str(stable),importable_object_sha256=sha(stable),
  scope='Conditional rational arithmetic only. The two cycle caps and charging formula remain premises; no endpoint theorem or actual-snake upper bound.')
save()
if ok:(H/'data/independent-credit-audit.json').write_bytes(record.read_bytes())
print(json.dumps(dict(status=state['status'],seconds=state['seconds'],axioms=reports,record=str(record))))
sys.exit(0 if ok else 1)
