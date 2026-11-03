"""Trim and independently replay the completed core LRAT, then map to the full CNF."""
from pathlib import Path
import hashlib,importlib.util,json,time
HERE=Path(__file__).resolve().parents[1];ROOT=HERE.parents[1]
read=lambda p:json.loads(p.read_text(encoding='utf-8-sig'))
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
solver=read(HERE/'data/extracted-core-scratch-solver.json')
assert solver['status']=='UNSAT_LRAT_UNCHECKED'
raw=HERE/solver['raw'];assert sha(raw)==solver['raw_sha256']
corepath=HERE/'work/extracted-core/core.cnf';assert sha(corepath)==solver['core_cnf_sha256']
core=[[int(x) for x in l.split()[:-1]] for l in corepath.read_text().splitlines() if l and not l.startswith(('c','p'))]
fullpath=HERE/'work/012310-total18/full.cnf'
full=[[int(x) for x in l.split()[:-1]] for l in fullpath.read_text().splitlines() if l and not l.startswith(('c','p'))]
mapping=solver['input_ids'];assert len(core)==len(mapping)==5431
assert core==[full[i-1] for i in mapping]
generator=ROOT/'milestones/109-relaxed-graph-test/upstream/milestones/10-window-aggregate/scripts/gen_lean_core.py'
sp=importlib.util.spec_from_file_location('core114',generator);module=importlib.util.module_from_spec(sp);sp.loader.exec_module(module)
trim=raw.with_name('core.trim.lrat');assert not trim.exists()
start=time.monotonic();nl,nh,ids=module.trim_lrat(str(raw),str(trim),len(core))
print('TRIMMED',len(ids),'inputs',nl,'steps',nh,'hints',flush=True)
def replay(path,clauses,input_ids):
    db={i:clauses[i-1] for i in input_ids};last=len(clauses);steps=hints=0
    with path.open() as f:
        for line in f:
            row=list(map(int,line.split()));z=row.index(0,1)
            cid,clause,hs=row[0],row[1:z],row[z+1:-1]
            assert row[-1]==0 and cid>last and all(0<h<cid for h in hs)
            assigned={-x for x in clause};conflict=any(-x in assigned for x in assigned)
            for h in hs:
                premise=db[h]
                if conflict or any(x in assigned for x in premise):continue
                rest={x for x in premise if -x not in assigned}
                assert len(rest)<=1
                if not rest:conflict=True
                else:assigned.add(next(iter(rest)))
            assert conflict
            db[cid]=clause;last=cid;steps+=1;hints+=len(hs)
    assert db[last]==[] and steps==nl and hints==nh
replay(trim,core,ids)
mapped=HERE/'work/012310-total18/full.trim.lrat';assert not mapped.exists()
def cid(i):return mapping[i-1] if i<=len(core) else len(full)+i-len(core)
with trim.open() as src,mapped.open('w',encoding='ascii',newline='\n') as dst:
    for line in src:
        row=list(map(int,line.split()));z=row.index(0,1)
        dst.write(' '.join(map(str,[cid(row[0]),*row[1:z],0,*map(cid,row[z+1:-1]),0]))+'\n')
fullids=sorted(mapping[i-1] for i in ids)
replay(mapped,full,fullids)
probe_path=HERE/'data/probes/012310-total18.json';probe=read(probe_path)
window=[0]
for d in probe['directions']:window.append(window[-1]^(1<<d))
target=HERE/'data/012310-total18-certificate.json';assert not target.exists()
out=dict(status='NATIVE_SUM_CERTIFICATE_REPLAYED_LEAN_PENDING',directions=probe['directions'],window=window,
    bounds=probe['bounds'],positions=probe['positions'],sum_cap=probe['cap'],cycle_cuts=probe['cycle_cuts'],
    variables=solver['variables'],clauses=len(full),core_ids=fullids,core_clauses=len(fullids),lemmas=nl,hints=nh,
    literal_occurrences=probe['literal_occurrences'],distinct_literals=probe['distinct_literals'],
    cnf_sha256=sha(fullpath),lrat_sha256=sha(mapped),local_trim_sha256=sha(trim),probe_sha256=sha(probe_path),
    solver_record_sha256=sha(HERE/'data/extracted-core-scratch-solver.json'),trimming_generator_sha256=sha(generator),
    script_sha256=sha(Path(__file__)),seconds=time.monotonic()-start,
    scope='RUP independently replayed both for the selected core and after mapping every input and deduction ID to the full native CNF. Concrete Lean counter semantics, proof replay and actual-snake theorem remain pending.')
target.write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')
print(out['status'],round(out['seconds'],3),flush=True)
