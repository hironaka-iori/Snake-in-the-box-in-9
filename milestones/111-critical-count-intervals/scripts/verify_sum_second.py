"""A second, longer independent check of the completed DRAT, with separate outputs."""
from pathlib import Path
import hashlib,json,subprocess,time
HERE=Path(__file__).resolve().parents[1];ROOT=HERE.parents[1]
read=lambda p:json.loads(p.read_text(encoding='utf-8-sig'));sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
source=read(HERE/'data/sum21-c153.json');prior=read(HERE/'data/sum21-drat-verification.json')
assert source['status']=='UNSAT_UNCERTIFIED' and prior['status']=='TIMEOUT'
cnf=HERE/'work/sum21/full.cnf';drat=HERE/'work/sum21-c153/proof.drat'
assert sha(cnf)==source['cnf_sha256'] and sha(drat)==source['drat_sha256']
record=HERE/'data/sum21-drat-verification-second.json';assert not record.exists()
outdir=HERE/'work/sum21-verified';outdir.mkdir(exist_ok=True)
exe=ROOT/'work/share-wheels/drat-trim.exe';log=HERE/'logs/sum21-drat-second.txt'
args=[str(exe),str(cnf),str(drat),'-L',str(outdir/'proof.lrat'),'-c',str(outdir/'core.cnf')]
out=dict(command=args,verifier_sha256=sha(exe),input_sha256=sha(cnf),drat_sha256=sha(drat),timeout_seconds=180,
    status='RUNNING',script_sha256=sha(Path(__file__)))
record.write_text(json.dumps(out,indent=2)+'\n');start=time.monotonic()
try:
    with log.open('w') as f:
        p=subprocess.run(args,stdout=f,stderr=subprocess.STDOUT,timeout=180)
    out.update(status='VERIFIED' if p.returncode==0 and 's VERIFIED' in log.read_text() else 'FAILED',exit_code=p.returncode)
except subprocess.TimeoutExpired:out['status']='TIMEOUT'
finally:
    out.update(seconds=time.monotonic()-start,log_sha256=sha(log))
    out['outputs']={p.name:dict(sha256=sha(p),bytes=p.stat().st_size) for p in outdir.iterdir() if p.is_file()}
    record.write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out,indent=2));assert out['status']=='VERIFIED'
