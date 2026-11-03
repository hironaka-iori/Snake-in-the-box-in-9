"""Build the already vendored checker, run controls, and verify/convert the saved DRAT."""
from pathlib import Path
import hashlib,json,subprocess,time
HERE=Path(__file__).resolve().parents[1];ROOT=HERE.parents[1]
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
record=HERE/'data/drat-conversion-bootstrap.json';assert not record.exists()
folder=HERE/'work/drat-conversion-bootstrap';folder.mkdir(exist_ok=True)
build=HERE/'build-native';build.mkdir(exist_ok=True)
compiler=Path('C:/Users/hironakaiori/AppData/Local/Temp/pip-target-rhmo53tp/lib/python/ziglang/zig.exe')
source=ROOT/'work/keep96/vendor/drat-trim/drat-trim.c'
assert sha(source)=='d834b649f437e091597f5347f259b9f681087f89ca0844d0cee250a1a1a0c2ee'
exe=build/'drat-trim.exe'
command=[str(compiler),'cc',str(source),'-O2','-std=c99','-Dgetc_unlocked=getc','-o',str(exe)]
log=HERE/'logs/drat-build-bootstrap.log';assert not log.exists()
with log.open('w') as f:proc=subprocess.run(command,stdout=f,stderr=subprocess.STDOUT,timeout=60)
out=dict(status='BUILD_FAILED',compiler=str(compiler),compiler_sha256=sha(compiler),source=str(source),source_sha256=sha(source),
    command=command,build_exit=proc.returncode,build_log_sha256=sha(log),script_sha256=sha(Path(__file__)))
def save():record.write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')
save();assert proc.returncode==0,log.read_text()
out['checker_sha256']=sha(exe)
controls=[]
for name,cnf,proof,expected in [
    ('valid','p cnf 2 4\n1 2 0\n1 -2 0\n-1 2 0\n-1 -2 0\n','1 0\n0\n',True),
    ('invalid','p cnf 2 1\n1 2 0\n','0\n',False),
    ('truncated','p cnf 2 4\n1 2 0\n1 -2 0\n-1 2 0\n-1 -2 0\n','',False)]:
    c=folder/(name+'.cnf');p=folder/(name+'.drat');l=folder/(name+'.lrat')
    c.write_text(cnf);p.write_text(proof)
    run=subprocess.run([str(exe),str(c),str(p),'-L',str(l)],capture_output=True,timeout=20)
    lp=folder/(name+'.log');lp.write_bytes(run.stdout+run.stderr)
    verified=run.returncode==0 and b's VERIFIED' in run.stdout
    assert verified==expected
    controls.append(dict(name=name,exit_code=run.returncode,verified=verified,expected=expected,log_sha256=sha(lp)))
out.update(status='CONTROLS_PASSED',controls=controls);save()
native=json.loads((HERE/'data/012310-total18-cadical153.json').read_text())
assert native['status']=='UNSAT_DRAT_UNCHECKED'
cnf=HERE/native['cnf'];drat=HERE/native['proof']
assert sha(cnf)==native['cnf_sha256'] and sha(drat)==native['proof_sha256']
lrat=folder/'full.lrat';core=folder/'core.cnf'
assert not lrat.exists() and not core.exists()
command=[str(exe),str(cnf),str(drat),'-L',str(lrat),'-c',str(core),'-t','120']
out.update(status='RUNNING',conversion_command=command,cnf_sha256=sha(cnf),drat_sha256=sha(drat));save()
log=HERE/'logs/drat-conversion-bootstrap.log';start=time.monotonic();code=None
with log.open('w') as f:
    try:code=subprocess.run(command,stdout=f,stderr=subprocess.STDOUT,timeout=125).returncode
    except subprocess.TimeoutExpired:pass
text=log.read_text(errors='replace')
out.update(status='PASS_NATIVE_DRAT_LRAT_CONVERSION' if code==0 and 's VERIFIED' in text else 'TIMEOUT_OR_FAILED',
    exit_code=code,seconds=time.monotonic()-start,log_sha256=sha(log),
    artifacts=[dict(path=p.relative_to(HERE).as_posix(),bytes=p.stat().st_size,sha256=sha(p)) for p in [lrat,core] if p.exists()],
    scope='Native checker with valid/invalid/truncated controls. Output still requires independent RUP replay, concrete semantics and Lean replay.')
save();print(out['status'],round(out['seconds'],3),flush=True)
