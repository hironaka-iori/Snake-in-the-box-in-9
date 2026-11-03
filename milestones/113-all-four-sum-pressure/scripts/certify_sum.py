"""Produce a bounded native certificate for a saved count-sum probe."""
from pathlib import Path
from itertools import combinations
import argparse, hashlib, importlib.util, json, subprocess, sys, time
HERE = Path(__file__).resolve().parents[1]
ROOT = HERE.parents[1]
read = lambda p: json.loads(p.read_text(encoding='utf-8-sig'))
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
ap = argparse.ArgumentParser()
ap.add_argument('case')
ap.add_argument('--seconds',type=int,default=30)
args = ap.parse_args()
sys.path.insert(0,str(ROOT/'milestones/10-window-aggregate/scripts'))
from gen_lean_sat import TaggedEncoding, is_cycle_set
from wincert import window_from_dirs
probe_path = HERE/'data/probes'/(args.case+'.json')
case = read(probe_path)
assert case['status'] == 'UNSAT_UNCERTIFIED'
enc = TaggedEncoding(window_from_dirs(case['directions']),[tuple(b) for b in case['bounds']],radius=4)
lits = []
for j in case['positions']:
    i = j+1
    v = enc.window[i]
    used = {v^enc.window[i-1],v^enc.window[i+1]}
    lits += [-enc.var[v^(1<<a)^(1<<b)] for a,b in combinations(range(9),2) if (1<<a) not in used and (1<<b) not in used]
lits.sort()
enc.atmost(lits,case['cap'],('unproved_sum',))
assert len(enc.clauses) == case['clauses'] and enc.nv == case['variables']
for cut in case['cycle_cuts']:
    assert is_cycle_set(cut)
    enc.add([-enc.var[v] for v in cut],('cut',))
work = HERE/'work'/args.case
work.mkdir(parents=True,exist_ok=True)
(HERE/'logs').mkdir(exist_ok=True)
record = HERE/'data'/(args.case+'-solver.json')
assert not record.exists()
cnf,raw,trim = work/'full.cnf',work/'full.raw.lrat',work/'full.trim.lrat'
assert not raw.exists()
cnf.write_bytes((f'p cnf {enc.nv} {len(enc.clauses)}\n'+''.join(' '.join(map(str,c))+' 0\n' for c in enc.clauses)).encode())
exe = Path('D:/Codex/2026-10-01/it-should-have-a-property-of/work/lean-research/lean-4.19.0-windows/bin/cadical.exe')
command = [str(exe),'-q','--lrat','--no-binary','--seed=1',str(cnf),str(raw)]
t = time.monotonic()
out = dict(command=command,solver_sha256=sha(exe),cnf_sha256=sha(cnf),timeout_seconds=args.seconds,
    probe_sha256=sha(probe_path),script_sha256=sha(Path(__file__)))
stdout,stderr = HERE/'logs'/(args.case+'-solver.stdout.txt'),HERE/'logs'/(args.case+'-solver.stderr.txt')
try:
    proc = subprocess.run(command,capture_output=True,timeout=args.seconds)
    stdout.write_bytes(proc.stdout)
    stderr.write_bytes(proc.stderr)
    out.update(status='NATIVE_UNSAT_LEAN_PENDING' if proc.returncode == 20 and b's UNSATISFIABLE' in proc.stdout else 'FAILED',exit_code=proc.returncode)
except subprocess.TimeoutExpired as exc:
    stdout.write_bytes(exc.stdout or b'')
    stderr.write_bytes(exc.stderr or b'')
    out.update(status='TIMEOUT')
out.update(seconds=time.monotonic()-t,stdout_sha256=sha(stdout),stderr_sha256=sha(stderr))
if raw.exists():
    out.update(raw_sha256=sha(raw),raw_bytes=raw.stat().st_size)
record.write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')
print(args.case,out['status'],round(out['seconds'],3),flush=True)
if out['status'] != 'NATIVE_UNSAT_LEAN_PENDING':
    sys.exit(0)
path = ROOT/'milestones/109-relaxed-graph-test/upstream/milestones/10-window-aggregate/scripts/gen_lean_core.py'
sp = importlib.util.spec_from_file_location('trim112',path)
gen = importlib.util.module_from_spec(sp)
sp.loader.exec_module(gen)
nl,nh,ids = gen.trim_lrat(str(raw),str(trim),len(enc.clauses))
core = work/'core.cnf'
core.write_bytes((f'p cnf {enc.nv} {len(ids)}\n'+''.join(' '.join(map(str,enc.clauses[i-1]))+' 0\n' for i in ids)).encode())
db = {i:enc.clauses[i-1] for i in ids}
last = len(enc.clauses)
added = hints = 0
with trim.open() as f:
    for line in f:
        row = list(map(int,line.split()))
        z = row.index(0,1)
        cid,clause,hs = row[0],row[1:z],row[z+1:-1]
        assert row[-1] == 0 and cid > last and all(0<h<cid for h in hs)
        assigned = {-x for x in clause}
        contradiction = any(-x in assigned for x in assigned)
        for h in hs:
            premise = db[h]
            if contradiction or any(x in assigned for x in premise):
                continue
            rest = {x for x in premise if -x not in assigned}
            assert len(rest) <= 1
            if not rest:
                contradiction = True
            else:
                assigned.add(next(iter(rest)))
        assert contradiction
        db[cid] = clause
        last = cid
        added += 1
        hints += len(hs)
assert db[last] == [] and added == nl and hints == nh
meta = dict(status='NATIVE_SUM_CERTIFICATE_REPLAYED_LEAN_PENDING',window=enc.window,bounds=case['bounds'],directions=case['directions'],
    positions=case['positions'],sum_cap=case['cap'],sum_counter=len(enc.ctrs)-1,literal_occurrences=len(lits),distinct_literals=len(set(lits)),
    variables=enc.nv,clauses=len(enc.clauses),core_ids=ids,core_clauses=len(ids),lemmas=nl,hints=nh,
    cnf_sha256=sha(cnf),core_sha256=sha(core),lrat_sha256=sha(trim),probe_sha256=sha(probe_path),
    trimming_generator_sha256=sha(path),script_sha256=sha(Path(__file__)),
    scope='Exact native CNF and trimmed RUP contradiction verified. Concrete sum semantics, Lean replay and actual-snake transfer remain pending.')
(HERE/'data'/(args.case+'-certificate.json')).write_text(json.dumps(meta,indent=2)+'\n',encoding='utf-8')
print('RUP_PASS',len(ids),'clauses',nl,'steps',nh,'hints',flush=True)
