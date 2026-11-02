"""Fresh bounded proof production for the proposed sum inequality; no Lean claim."""
from pathlib import Path
from itertools import combinations
import hashlib,importlib.util,json,subprocess,sys,time
HERE=Path(__file__).resolve().parents[1];ROOT=HERE.parents[1]
read=lambda p:json.loads(p.read_text(encoding='utf-8-sig'));sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
sys.path.insert(0,str(ROOT/'milestones/10-window-aggregate/scripts'))
from gen_lean_sat import TaggedEncoding
from wincert import window_from_dirs
case=read(HERE/'data/probes/outer-sum21.json');assert case['status']=='UNSAT_UNCERTIFIED' and not case['cycle_cuts']
enc=TaggedEncoding(window_from_dirs(case['directions']),[tuple(b) for b in case['bounds']],radius=4)
lits=[]
for i in [1,2,4,5]:
    c=enc.window[i];used={c^enc.window[i-1],c^enc.window[i+1]}
    lits += [-enc.var[c^(1<<a)^(1<<b)] for a,b in combinations(range(9),2) if (1<<a) not in used and (1<<b) not in used]
assert len(lits)==84;enc.atmost(lits,21,('unproved_sum',))
work=HERE/'work/sum21';work.mkdir(parents=True,exist_ok=True)
cnf=work/'full.cnf';cnf.write_bytes((f'p cnf {enc.nv} {len(enc.clauses)}\n'+''.join(' '.join(map(str,c))+' 0\n' for c in enc.clauses)).encode())
assert len(enc.clauses)==case['clauses'] and enc.nv==case['variables']
raw=work/'full.raw.lrat';record=HERE/'data/sum21-solver.json';assert not record.exists() and not raw.exists()
exe=Path('D:/Codex/2026-10-01/it-should-have-a-property-of/work/lean-research/lean-4.19.0-windows/bin/cadical.exe')
args=[str(exe),'-q','--lrat','--no-binary','--seed=1',str(cnf),str(raw)]
t=time.monotonic();out=dict(command=args,solver_sha256=sha(exe),cnf_sha256=sha(cnf),timeout_seconds=60,script_sha256=sha(Path(__file__)))
try:
    p=subprocess.run(args,capture_output=True,text=True,timeout=60)
    (HERE/'logs/sum21-solver.stdout.txt').write_text(p.stdout,encoding='utf-8');(HERE/'logs/sum21-solver.stderr.txt').write_text(p.stderr,encoding='utf-8')
    out.update(status='NATIVE_UNSAT_LEAN_PENDING' if p.returncode==20 and 's UNSATISFIABLE' in p.stdout else 'FAILED',exit_code=p.returncode,seconds=time.monotonic()-t)
except subprocess.TimeoutExpired as exc:
    out.update(status='TIMEOUT',seconds=time.monotonic()-t)
    (HERE/'logs/sum21-solver.stdout.txt').write_bytes(exc.stdout or b'');(HERE/'logs/sum21-solver.stderr.txt').write_bytes(exc.stderr or b'')
finally:
    if raw.exists():out.update(raw_sha256=sha(raw),raw_bytes=raw.stat().st_size)
    record.write_text(json.dumps(out,indent=2)+'\n')
assert out['status']=='NATIVE_UNSAT_LEAN_PENDING',out
path=ROOT/'milestones/109-relaxed-graph-test/upstream/milestones/10-window-aggregate/scripts/gen_lean_core.py'
spec=importlib.util.spec_from_file_location('core111',path);gen=importlib.util.module_from_spec(spec);spec.loader.exec_module(gen)
trim=work/'full.trim.lrat';nl,nh,ids=gen.trim_lrat(str(raw),str(trim),len(enc.clauses))
core=work/'core.cnf';core.write_bytes((f'p cnf {enc.nv} {len(ids)}\n'+''.join(' '.join(map(str,enc.clauses[i-1]))+' 0\n' for i in ids)).encode())
meta=dict(status='NATIVE_SUM_CONTRADICTION_LEAN_PENDING',window=enc.window,bounds=case['bounds'],directions=case['directions'],
    outer_indices=[0,1,3,4],sum_cap=21,sum_counter=len(enc.ctrs)-1,variables=enc.nv,clauses=len(enc.clauses),core_ids=ids,
    core_clauses=len(ids),lemmas=nl,hints=nh,full_sha256=sha(cnf),core_sha256=sha(core),lrat_sha256=sha(trim),
    generator_sha256=sha(path),probe_sha256=sha(HERE/'data/probes/outer-sum21.json'),
    scope='Native LRAT and extracted core. A new general-counter semantic application and checked contradiction are required.')
(HERE/'data/sum21-core.json').write_text(json.dumps(meta,indent=2)+'\n')
print(json.dumps({k:v for k,v in meta.items() if k!='core_ids'},indent=2))
