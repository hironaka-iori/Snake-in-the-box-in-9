"""Bounded Lean experiment with exact receipts and an active memory limit."""
from pathlib import Path
import argparse, hashlib, json, os, re, subprocess, time

H=Path(__file__).resolve().parents[1]; R=H.parents[1]
B=Path('D:/Codex/2026-10-01/it-should-have-a-property-of/work/lean-research/lean-4.19.0-windows/bin')
read=lambda p:json.loads(Path(p).read_text(encoding='utf-8-sig'))
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
ap=argparse.ArgumentParser();ap.add_argument('module');ap.add_argument('--timeout',type=int,default=120)
a=ap.parse_args();assert re.fullmatch(r'[A-Za-z][A-Za-z0-9.]*',a.module)
src=H/'lean'/(a.module.replace('.','/')+'.lean')
source=src.read_text();assert not re.search(r'\b(sorry|admit|native_decide|axiom)\b',source)
ef=R/'milestones/125-critical-six-count/data/environment-sum.json'; e=read(ef)
build=H/'build-independent';build.mkdir(parents=True,exist_ok=True)
paths=[str(build),str(R/'milestones/145-countfree-012301/build-independent'),str(R/'milestones/144-countfree-share18/build-base'),str(R/'milestones/144-countfree-share18/experiments/build'),str(B.parent.parent/'mathlib/.lake/build/lib/lean')]+e['paths']
deps={str(ef):sha(ef),str(B/'lean.exe'):sha(B/'lean.exe'),str(B/'lake.exe'):sha(B/'lake.exe')}
for p,d in e['receipts'].items():assert sha(R/p)==d;deps[str(R/p)]=d
for m in re.findall(r'^import ([\w.]+)$',source,re.M):
 obj=next((Path(p)/(m.replace('.','/')+'.olean') for p in paths if (Path(p)/(m.replace('.','/')+'.olean')).exists()),None)
 assert obj is not None,m
 deps[str(obj)]=sha(obj)
 rp=H/'data'/(m+'-audit.json')
 if not rp.exists():rp=R/'milestones/145-countfree-012301/data'/(m+'-audit.json')
 if not rp.exists():rp=R/'milestones/144-countfree-share18/data'/(m+'-audit.json')
 if not rp.exists():rp=R/'milestones/144-countfree-share18/experiments/data'/(m+'-audit.json')
 if not rp.exists():
  assert m.startswith('Mathlib.'),m
  continue
 q=read(rp);assert q['exit_code']==0 and q['olean_sha256']==sha(obj)
 deps[str(rp)]=sha(rp)
 for p,d in q['dependencies'].items():
  p=Path(p);p=p if p.is_absolute() else R/p
  assert sha(p)==d,p;deps[str(p)]=d

def resources(parent=0):
 cmd="$o=Get-CimInstance Win32_OperatingSystem;$p=@(Get-CimInstance Win32_Process -Filter \"Name='lean.exe'\"|Select-Object ProcessId,ParentProcessId,PrivatePageCount);@{free_bytes=[long]$o.FreePhysicalMemory*1024;processes=$p}|ConvertTo-Json -Depth 3 -Compress"
 return json.loads(subprocess.check_output(['powershell','-NoProfile','-Command',cmd],text=True))
gate=resources();assert gate['free_bytes']>=1.5*1024**3 and len(gate['processes'])<=2,gate
run=str(time.time_ns());outdir=H/'logs'/(a.module+'-'+run);outdir.mkdir(parents=True)
obj=build/(a.module.replace('.','/')+'.'+run+'.olean');obj.parent.mkdir(parents=True,exist_ok=True)
log=outdir/'compiler.log';rec=outdir/'record.json'
(outdir/'source.lean.txt').write_bytes(src.read_bytes());(outdir/'checker.py.txt').write_bytes(Path(__file__).read_bytes())
state=dict(status='RUNNING',pid=os.getpid(),source=str(src),source_sha256=sha(src),dependencies=deps,
 checker_sha256=sha(__file__),resource_gate=gate,resource_samples=[],timeout_seconds=a.timeout,
 memory_limit_bytes=3*1024**3,minimum_free_bytes=768*1024**2,log=str(log),paths=paths)
def save():rec.write_text(json.dumps(state,indent=2)+'\n')
env=os.environ.copy();env['PATH']=str(B)+';'+env['PATH'];env['LEAN_PATH']=';'.join(paths)
cmd=[str(B/'lake.exe'),'env','lean','-s','65536','-R',str(H/'lean'),'-o',str(obj),str(src)]
state['command']=cmd;save();start=time.monotonic();stop=None
with log.open('w',encoding='utf-8') as f:
 child=subprocess.Popen(cmd,cwd=B.parent.parent/'mathlib',env=env,stdout=f,stderr=subprocess.STDOUT)
 state['launcher_pid']=child.pid;save()
 while child.poll() is None:
  if time.monotonic()-start>a.timeout:stop='TIMEOUT'
  snap=resources();snap['seconds']=time.monotonic()-start
  own=[p for p in snap['processes'] if int(p['ParentProcessId'])==child.pid]
  snap['owned_lean_processes']=own;state['resource_samples'].append(snap);save()
  if any(int(p['PrivatePageCount'])>state['memory_limit_bytes'] for p in own):stop='MEMORY_LIMIT'
  if snap['free_bytes']<state['minimum_free_bytes']:stop='LOW_FREE_MEMORY'
  if stop:
   subprocess.run(['taskkill','/PID',str(child.pid),'/T','/F'],stdout=subprocess.DEVNULL,stderr=subprocess.DEVNULL)
   break
  time.sleep(2)
 code=child.wait(timeout=30)
output=log.read_text(encoding='utf-8')
reports=[dict(theorem=n,axioms=re.findall(r'[A-Za-z][\w.]*',x)) for n,x in re.findall(r"'([^']+)' depends on axioms:\s*\[([^]]*)\]",output,re.S)]
reports += [dict(theorem=n,axioms=[]) for n in re.findall(r"'([^']+)' does not depend on any axioms",output)]
ok=code==0 and stop is None and 'error:' not in output and 'sorryAx' not in output
ok=ok and len(reports)==source.count('#print axioms') and all(set(q['axioms'])<={'propext','Classical.choice','Quot.sound'} for q in reports)
ok=ok and sha(src)==state['source_sha256'] and sha(__file__)==state['checker_sha256'] and all(sha(p)==d for p,d in deps.items())
state.update(status='PASS' if ok else 'FAILED',exit_code=code,stop_reason=stop,seconds=time.monotonic()-start,axioms=reports,log_sha256=sha(log))
if ok:
 stable=build/(a.module.replace('.','/')+'.olean');stable.write_bytes(obj.read_bytes())
 state.update(olean_sha256=sha(stable),object=str(stable))
save()
if ok:
 rp=H/'data'/(a.module+'-audit.json');rp.parent.mkdir(exist_ok=True);rp.write_bytes(rec.read_bytes())
print(json.dumps({k:state[k] for k in ['status','seconds','stop_reason','axioms']}),flush=True)
raise SystemExit(0 if ok else 1)
