"""Check the extracted clause subset and seek a smaller direct LRAT contradiction."""
from pathlib import Path
from collections import defaultdict,deque
import hashlib,json,subprocess,time
HERE=Path(__file__).resolve().parents[1]
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
def formula(path):
    rows=[];variables=count=None
    for line in path.read_text().splitlines():
        if line.startswith('p '):_,_,variables,count=line.split()
        elif line and not line.startswith('c'):
            row=list(map(int,line.split()));assert row[-1]==0;rows.append(row[:-1])
    assert len(rows)==int(count)
    return int(variables),rows
full=HERE/'work/012310-total18/full.cnf';core=HERE/'work/drat-conversion-bootstrap/core.cnf'
nv,clauses=formula(full);cv,subset=formula(core);assert nv==cv
available=defaultdict(deque)
for i,c in enumerate(clauses,1):available[tuple(c)].append(i)
ids=[]
for c in subset:
    assert available[tuple(c)],'Extracted clause is not an original input'
    ids.append(available[tuple(c)].popleft())
assert len(ids)==len(set(ids))
folder=HERE/'work/extracted-core';folder.mkdir(exist_ok=True)
copy=folder/'core.cnf';assert not copy.exists();copy.write_bytes(core.read_bytes())
assert formula(copy)==(nv,subset)
raw=folder/'core.raw.lrat';assert not raw.exists()
record=HERE/'data/extracted-core-solver.json';assert not record.exists()
exe=Path('D:/Codex/2026-10-01/it-should-have-a-property-of/work/lean-research/lean-4.19.0-windows/bin/cadical.exe')
command=[str(exe),'-q','--lrat','--no-binary','--seed=1',str(copy),str(raw)]
out=dict(status='RUNNING',command=command,solver_sha256=sha(exe),script_sha256=sha(Path(__file__)),
    full_cnf_sha256=sha(full),core_cnf_sha256=sha(copy),input_ids=ids,variables=nv,clauses=len(ids),
    scope='Every extracted clause is checked against an original input. This run does not depend on the success of the native DRAT conversion; only its own completed contradiction can establish UNSAT.')
def save():record.write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')
save();start=time.monotonic();stdout=HERE/'logs/extracted-core.stdout.log';stderr=HERE/'logs/extracted-core.stderr.log'
try:
    p=subprocess.run(command,capture_output=True,timeout=60)
    stdout.write_bytes(p.stdout);stderr.write_bytes(p.stderr)
    out.update(status='UNSAT_LRAT_UNCHECKED' if p.returncode==20 and b's UNSATISFIABLE' in p.stdout else 'FAILED',exit_code=p.returncode)
except subprocess.TimeoutExpired as e:
    stdout.write_bytes(e.stdout or b'');stderr.write_bytes(e.stderr or b'');out['status']='TIMEOUT'
out.update(seconds=time.monotonic()-start,stdout_sha256=sha(stdout),stderr_sha256=sha(stderr))
if raw.exists():out.update(raw_sha256=sha(raw),raw_bytes=raw.stat().st_size)
save();print(out['status'],out['clauses'],round(out['seconds'],3),flush=True)
