"""Check the standalone rational comparison and preserve every attempt."""
from pathlib import Path
import datetime, hashlib, json, os, re, subprocess, time
HERE=Path(__file__).resolve().parents[1]
BIN=Path('D:/Codex/2026-10-01/it-should-have-a-property-of/work/lean-research/lean-4.19.0-windows/bin')
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
name='PotentialComparison';run=str(time.time_ns())
src=HERE/'lean'/(name+'.lean')
(HERE/'build').mkdir(exist_ok=True)
obj=HERE/'build'/(name+'.olean');fresh=obj.with_name(name+'.'+run+'.olean')
log=HERE/'logs'/(name+'-'+run+'.log')
env=os.environ.copy();env['PATH']=str(BIN)+';'+env['PATH'];env.pop('LEAN_PATH',None)
before=sha(src);checker=sha(Path(__file__));start=time.monotonic();timeout=False
version=subprocess.check_output([str(BIN/'lean.exe'),'--version'],text=True).strip()
cmd=[str(BIN/'lake.exe'),'env','lean','-s','65536','-R',str(HERE/'lean'),'-o',str(fresh),str(src)]
with log.open('w',encoding='utf-8') as out:
    proc=subprocess.Popen(cmd,cwd=BIN.parent.parent/'mathlib',env=env,stdout=out,stderr=subprocess.STDOUT)
    try:code=proc.wait(timeout=180)
    except subprocess.TimeoutExpired:
        timeout=True
        subprocess.run(['taskkill','/PID',str(proc.pid),'/T','/F'],stdout=subprocess.DEVNULL,stderr=subprocess.DEVNULL,check=False)
        code=proc.wait(timeout=30)
r=dict(module=name,exit_code=code,seconds=time.monotonic()-start,timeout=timeout,
       recorded_at=datetime.datetime.now(datetime.timezone.utc).isoformat(),lean_version=version,
       source_sha256=before,checker_sha256=checker,log=log.relative_to(HERE).as_posix(),log_sha256=sha(log),command=cmd)
(HERE/'logs'/(name+'-'+run+'-record.json')).write_text(json.dumps(r,indent=2)+'\n')
assert not timeout and code==0,log.read_text()[-16000:]
assert sha(src)==before and sha(Path(__file__))==checker
output=log.read_text();assert 'error:' not in output and 'sorryAx' not in output
assert not re.search(r'\b(sorry|admit|native_decide)\b',src.read_text())
matches=re.findall(r"'([^']+)' depends on axioms:\s*\[([^]]*)\]",output,re.S)
matches += [(n,'') for n in re.findall(r"'([^']+)' does not depend on any axioms",output)]
assert len(matches)==7==src.read_text().count('#print axioms')
audits=[]
for theorem,values in matches:
    axioms=re.findall(r'[A-Za-z][\w.]*',values)
    assert set(axioms)<={'propext','Classical.choice','Quot.sound'}
    audits.append(dict(theorem=theorem,axioms=axioms))
os.replace(fresh,obj)
r.update(status='PASS_RATIONAL_POTENTIAL_COMPARISON',olean_sha256=sha(obj),theorem_audits=audits,
         scope='General telescoping and joint comparison, plus three conditional rational instantiations. Concrete graph embedding and weight-to-share semantics are separate.')
(HERE/'data'/(name+'-audit.json')).write_text(json.dumps(r,indent=2)+'\n')
print(r['status'],round(r['seconds'],3),'seconds; 7 theorem audits',flush=True)
