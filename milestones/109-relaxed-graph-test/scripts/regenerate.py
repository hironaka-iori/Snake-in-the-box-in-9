"""Produce a small LRAT certificate for the exact recovered D01234A1542 core."""
from pathlib import Path
import ast,hashlib,importlib.util,json,re,subprocess,time
HERE=Path(__file__).resolve().parents[1];ROOT=HERE.parents[1]
UP=HERE/'upstream/milestones/10-window-aggregate/scripts'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
read=lambda p:json.loads(p.read_text(encoding='utf-8-sig'))
pins=read(HERE/'data/input-pins.json')
for row in pins['files']:assert sha(ROOT/row['saved'])==row['sha256']
corepath=HERE/'work/D01234A1542-core.cnf';assert sha(corepath)==pins['core_cnf_sha256']
meta=read(HERE/'upstream/milestones/10-window-aggregate/data/lean_core_direction5/d01234_a1_5_4_2.json')
source=(HERE/'lean/LocalWindowCnf/D01234A1542.lean').read_text()
body=re.split(r'(?:noncomputable )?def cnf',source.split('def raw : List (List Nat) :=',1)[1],maxsplit=1)[0].strip()
encoded=ast.literal_eval(body)
decoded=[[v//2 if v%2==0 else -(v//2) for v in c] for c in encoded]
full=[[int(v) for v in line.split()[:-1]] for line in (HERE/'work/d01234_a1_5_4_2.cnf').read_text().splitlines() if line and not line.startswith(('p','c'))]
assert decoded==[full[i-1] for i in meta['core_ids']]
assert len(decoded)==441 and len(full)==24359
assert meta['dirs']==[0,1,2,3,4] and meta['syms']==[1,5,4,2]
cadical=Path('D:/Codex/2026-10-01/it-should-have-a-property-of/work/lean-research/lean-4.19.0-windows/bin/cadical.exe')
raw=HERE/'work/D01234A1542.raw.lrat';record=HERE/'data/solver-attempt.json'
if record.exists():
    r=read(record);assert r['status']=='NATIVE_UNSAT_NOT_KERNEL_PROOF' and sha(raw)==r['proof_sha256']
else:
    assert not raw.exists()
    args=[str(cadical),'-q','--lrat','--no-binary','--seed=1',str(corepath),str(raw)]
    start=time.monotonic();r=dict(command=args,solver_sha256=sha(cadical),input_sha256=sha(corepath),timeout_seconds=60)
    try:
        proc=subprocess.run(args,capture_output=True,text=True,timeout=60)
        (HERE/'logs/cadical.stdout.txt').write_text(proc.stdout,encoding='utf-8')
        (HERE/'logs/cadical.stderr.txt').write_text(proc.stderr,encoding='utf-8')
        r.update(exit_code=proc.returncode,seconds=time.monotonic()-start,status='NATIVE_UNSAT_NOT_KERNEL_PROOF' if proc.returncode==20 and 's UNSATISFIABLE' in proc.stdout else 'FAILED')
        if raw.exists():r['proof_sha256']=sha(raw)
    except subprocess.TimeoutExpired as exc:
        r.update(status='TIMEOUT',seconds=time.monotonic()-start)
        raise
    finally:record.write_text(json.dumps(r,indent=2)+'\n',encoding='utf-8')
    assert r['status']=='NATIVE_UNSAT_NOT_KERNEL_PROOF',r
def load(path,name):
    spec=importlib.util.spec_from_file_location(name,path);module=importlib.util.module_from_spec(spec);spec.loader.exec_module(module);return module
coregen=load(UP/'gen_lean_core.py','pinned_core109')
trimmed=HERE/'work/D01234A1542.trimmed.lrat'
nl,nh,used=coregen.trim_lrat(str(raw),str(trimmed),len(decoded))
mapped=HERE/'work/d01234_a1_5_4_2.lrat'
ids=meta['core_ids'];ncore=len(ids);nfull=len(full)
def remap(i):return ids[i-1] if i<=ncore else i-ncore+nfull
with trimmed.open() as f,mapped.open('w',encoding='ascii',newline='\n') as g:
    for line in f:
        t=list(map(int,line.split()));z=t.index(0,1)
        assert all(h>0 for h in t[z+1:-1]) and t[-1]==0
        out=[remap(t[0]),*t[1:z],0,*map(remap,t[z+1:-1]),0]
        g.write(' '.join(map(str,out))+'\n')
generator=load(UP/'gen_lean_lrat.py','pinned_lrat109')
generator.set_width(13,fast=True,off=2400);generator.DATA_DEF='noncomputable def'
stats=generator.export('d01234_a1_5_4_2',str(HERE/'work'),6000,2,1,True,str(HERE/'lean'),str(HERE/'upstream/milestones/10-window-aggregate/data/lean_core_direction5'))
sources={p.relative_to(HERE).as_posix():sha(p) for p in sorted((HERE/'lean').rglob('*.lean'))}
out=dict(status='GENERATED_AND_SIMULATED_NOT_KERNEL_PROOF',decoded_core_matches_lean=True,
    core_clauses=ncore,full_clauses=nfull,trimmed_lemmas=nl,trimmed_hints=nh,used_core_clauses=len(used),
    raw_lrat_sha256=sha(raw),trimmed_lrat_sha256=sha(trimmed),mapped_lrat_sha256=sha(mapped),
    generation=stats,sources=sources,scope='Native UNSAT and independent core identity, LRAT generation and simulation only. Lean refutation and semantic composition remain unchecked.')
(HERE/'data/generation.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')
print(json.dumps({k:v for k,v in out.items() if k!='sources'},indent=2))
