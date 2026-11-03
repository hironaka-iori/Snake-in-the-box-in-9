"""Bounded Lean experiment with exact receipts and an active memory limit."""
from pathlib import Path
import argparse, hashlib, json, os, re, subprocess, time

H=Path(__file__).resolve().parents[1]; R=H.parents[1]
B=Path('D:/Codex/2026-10-01/it-should-have-a-property-of/work/lean-research/lean-4.19.0-windows/bin')
read=lambda p:json.loads(Path(p).read_text(encoding='utf-8-sig'))
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
ap=argparse.ArgumentParser();ap.add_argument('module');ap.add_argument('--timeout',type=int,default=120)
ap.add_argument('--prepare-overlay-only',action='store_true')
a=ap.parse_args();assert re.fullmatch(r'[A-Za-z][A-Za-z0-9.]*',a.module)
src=H/'lean'/(a.module.replace('.','/')+'.lean')
source=src.read_text(encoding='utf-8');assert not re.search(r'\b(sorry|admit|native_decide|axiom)\b',source)
ef=R/'milestones/125-critical-six-count/data/environment-sum.json'; e=read(ef)
build=H/'build-independent';build.mkdir(parents=True,exist_ok=True)
paths=[str(build),str(R/'milestones/145-countfree-012301/build-independent'),str(R/'milestones/144-countfree-share18/build-base'),str(R/'milestones/144-countfree-share18/experiments/build'),str(B.parent.parent/'mathlib/.lake/build/lib/lean')]+e['paths']
deps={str(ef):sha(ef),str(B/'lean.exe'):sha(B/'lean.exe'),str(B/'lake.exe'):sha(B/'lake.exe')}
for p,d in e['receipts'].items():assert sha(R/p)==d;deps[str(R/p)]=d

def semantic_overlay():
 """Merge legacy namespace objects without changing source or path precedence."""
 manifest=H/'data/semantic-import-overlay.json'
 roots=[Path(p) for p in paths[1:]]
 prefixes=['LocalWindowCnf','LocalWindowSat','LocalWindowUnsat']
 selected={};duplicates=0
 for priority,root in enumerate(roots):
  for prefix in prefixes:
   folder=root/prefix
   if not folder.is_dir():continue
   for obj in sorted(folder.rglob('*.olean')):
    rel=obj.relative_to(root)
    # Exclude compiler attempt files; each path component must be a module name.
    if not all(re.fullmatch(r'[A-Za-z_][A-Za-z0-9_]*',part) for part in rel.with_suffix('').parts):continue
    key=rel.as_posix()
    if key in selected:duplicates+=1;continue
    selected[key]=(obj,priority)
 assert len(selected)<=10000 and sum(p.stat().st_size for p,_ in selected.values())<=5*1024**3
 if manifest.exists():
  result=read(manifest)
  assert result['status']=='PASS_HASH_AUDITED_NAMESPACE_OVERLAY'
  assert result['ordered_source_paths']==[str(p) for p in roots]
  assert set(selected)=={x['relative_path'] for x in result['objects']}
 else:
  result=dict(status='PREPARING',ordered_source_paths=[str(p) for p in roots],prefixes=prefixes,
   objects=[],duplicate_candidates=duplicates,created_utc=time.strftime('%Y-%m-%dT%H:%M:%SZ',time.gmtime()),
   scope='Only existing compiled objects. First existing object in original ordered paths wins; proof sources and original objects are unchanged.')
  for rel,(origin,priority) in selected.items():
   target=build/rel;digest=sha(origin)
   target.parent.mkdir(parents=True,exist_ok=True)
   if target.exists():
    assert sha(target)==digest,('Refuse to overwrite a different existing object',target)
    mode='preserved_existing'
   else:
    os.link(origin,target);mode='hardlink'
   assert sha(target)==digest
   result['objects'].append(dict(relative_path=rel,source=str(origin),destination=str(target),
    source_priority=priority,sha256=digest,bytes=origin.stat().st_size,mode=mode))
  result.update(status='PASS_HASH_AUDITED_NAMESPACE_OVERLAY',object_count=len(selected),
   total_bytes=sum(x['bytes'] for x in result['objects']))
  temp=manifest.with_suffix('.pending.json')
  temp.write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8');os.replace(temp,manifest)
 for item in result['objects']:
  origin,priority=selected[item['relative_path']]
  assert str(origin)==item['source'] and priority==item['source_priority']
  assert sha(origin)==sha(item['destination'])==item['sha256']
  deps[item['source']]=item['sha256'];deps[item['destination']]=item['sha256']
 deps[str(manifest)]=sha(manifest)
 return result

overlay=semantic_overlay()
if a.prepare_overlay_only:
 print(json.dumps(dict(status=overlay['status'],objects=overlay['object_count'],bytes=overlay['total_bytes'])),flush=True)
 raise SystemExit(0)
for m in re.findall(r'^import ([\w.]+)$',source,re.M):
 obj=next((Path(p)/(m.replace('.','/')+'.olean') for p in paths if (Path(p)/(m.replace('.','/')+'.olean')).exists()),None)
 assert obj is not None,m
 deps[str(obj)]=sha(obj)
 rp=H/'data'/(m+'-audit.json')
 if not rp.exists():rp=R/'milestones/145-countfree-012301/data'/(m+'-audit.json')
 if not rp.exists():rp=R/'milestones/144-countfree-share18/data'/(m+'-audit.json')
 if not rp.exists():rp=R/'milestones/144-countfree-share18/experiments/data'/(m+'-audit.json')
 if not rp.exists():
  found=sorted({(R/p).resolve() for p in e['receipts'] if Path(p).name==m+'-audit.json'})
  if found:assert len(found)==1;rp=found[0]
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
gate=resources();assert gate['free_bytes']>=1.5*1024**3 and len(gate['processes'])==0,gate
run=str(time.time_ns());outdir=H/'logs'/(a.module+'-'+run);outdir.mkdir(parents=True)
obj=build/(a.module.replace('.','/')+'.'+run+'.olean');obj.parent.mkdir(parents=True,exist_ok=True)
log=outdir/'compiler.log';rec=outdir/'record.json'
(outdir/'source.lean.txt').write_bytes(src.read_bytes());(outdir/'checker.py.txt').write_bytes(Path(__file__).read_bytes())
state=dict(status='RUNNING',pid=os.getpid(),source=str(src),source_sha256=sha(src),dependencies=deps,
 checker_sha256=sha(__file__),resource_gate=gate,resource_samples=[],timeout_seconds=a.timeout,
 memory_limit_bytes=3*1024**3,minimum_free_bytes=768*1024**2,log=str(log),paths=paths,
 overlay_manifest=str(H/'data/semantic-import-overlay.json'),overlay_sha256=sha(H/'data/semantic-import-overlay.json'))
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
 stable=build/(a.module.replace('.','/')+'.olean');os.replace(obj,stable)
 state.update(olean_sha256=sha(stable),object=str(stable))
save()
if ok:
 rp=H/'data'/(a.module+'-audit.json');rp.parent.mkdir(exist_ok=True);rp.write_bytes(rec.read_bytes())
print(json.dumps({k:state[k] for k in ['status','seconds','stop_reason','axioms']}),flush=True)
raise SystemExit(0 if ok else 1)
