"""Independent square-indicator CP model and fixed-selection counter controls.

The CP model enumerates all 36 squares per centre. It does not use the SAT
counter or its reduction to 21 free opposite corners. Solver exclusions remain
experimental until a proof certificate is replayed in Lean.
"""
import hashlib, importlib.util, itertools, json, sys, time
from pathlib import Path
HERE=Path(__file__).resolve().parents[1]; ROOT=HERE.parents[1]
sys.path.insert(0,str(ROOT/'milestones/29-overlapping-share-windows/scripts'))
from joint import TaggedEncoding, Cadical153, candidates, window
sys.path.insert(0,str(ROOT/'work/solver_packages'))
from ortools.sat.python import cp_model
spec=importlib.util.spec_from_file_location('prior',ROOT/'milestones/28-direct-share-certificates/scripts/verify.py')
prior=importlib.util.module_from_spec(spec);spec.loader.exec_module(prior)
BOUNDS=[(6,21),(3,3),(3,3),(6,21),(3,3),(3,3),(6,21)]

def joint_literals(enc,W):
    out=[]
    for j in [1,4,7]:
        c=W[j];used={(c^W[j-1]).bit_length()-1,(c^W[j+1]).bit_length()-1}
        out.extend(-enc.var[c^(1<<a)^(1<<b)] for a,b in itertools.combinations(range(9),2) if a not in used and b not in used)
    assert len(out)==63
    return out

def controls():
    rows=[]
    for i in [2,3]:
        row=json.loads((ROOT/f'milestones/29-overlapping-share-windows/data/next-interval-{i}.json').read_text())
        c=prior.census(row); S=set(row['selected']); exact=sum(c['alpha'][j] for j in [0,3,6])
        for cap in [exact-1,exact]:
            enc=TaggedEncoding(window(row['dirs']),BOUNDS,radius=4)
            lits=joint_literals(enc,window(row['dirs']))
            assert sum(enc.meaning[abs(l)][1] not in S for l in lits)==exact
            enc.atmost(lits,cap,('jointSum',0))
            with Cadical153(bootstrap_with=enc.clauses) as solver:
                ok=solver.solve(assumptions=[enc.var[v] if v in S else -enc.var[v] for v in enc.ball])
            assert ok==(cap==exact)
            rows.append(dict(case=i,exact=exact,cap=cap,sat=ok,literal_occurrences=len(lits),distinct_literals=len(set(lits))))
    return rows

def solve(i,cap,seconds=15):
    ds=candidates()[i]['dirs'];W=window(ds);C=W[1:-1]
    B={v for v in range(512) if min((v^c).bit_count() for c in C)<=4}
    md=cp_model.CpModel();x={v:md.new_bool_var(f'x{v}') for v in sorted(B)}
    for v in W:md.add(x[v]==1)
    ends=[]
    for v in sorted(B):
        ns=[x[v^(1<<a)] for a in range(9) if (v^(1<<a)) in B]
        md.add(sum(ns)<=2).only_enforce_if(x[v])
        if len(ns)==9:
            e=md.new_bool_var(f'e{v}');ends.append(e);md.add(e<=x[v])
            md.add(sum(ns)==2-e).only_enforce_if(x[v])
    md.add(sum(ends)<=2)
    alphas=[]
    for j,c in enumerate(C):
        squares=[]
        for a,b in itertools.combinations(range(9),2):
            others=[c^(1<<a),c^(1<<b),c^(1<<a)^(1<<b)]
            z=md.new_bool_var(f's{j}_{a}_{b}');squares.append(z)
            md.add(sum(x[v] for v in others)==0).only_enforce_if(z)
            md.add(sum(x[v] for v in others)>=1).only_enforce_if(z.Not())
        total=sum(squares);alphas.append(total)
        md.add(total>=BOUNDS[j][0]);md.add(total<=BOUNDS[j][1])
    md.add(sum(alphas[j] for j in [0,3,6])<=cap)
    cuts=[];t=time.monotonic();status='UNKNOWN';selected=None;report=None
    while time.monotonic()-t<seconds:
        solver=cp_model.CpSolver();solver.parameters.max_time_in_seconds=max(.01,seconds-(time.monotonic()-t))
        solver.parameters.num_search_workers=2;solver.parameters.random_seed=196
        result=solver.solve(md);status=solver.status_name(result)
        if result not in (cp_model.OPTIMAL,cp_model.FEASIBLE):break
        S={v for v in B if solver.value(x[v])};cycles=[]
        for part in prior.components(S):
            if all(sum(w in S for w in prior.neighbors(v))==2 for v in part):cycles.append(sorted(part))
        if not cycles:
            selected=sorted(S);report=prior.census(dict(dirs=ds,alpha=BOUNDS,selected=selected))
            assert sum(report['alpha'][j] for j in [0,3,6])<=cap
            break
        for cc in cycles:
            prior.check_cut(cc);cuts.append(cc);md.add(sum(x[v] for v in cc)<=len(cc)-1)
    if selected is None and status in ('FEASIBLE','OPTIMAL'):status='TIME_LIMIT_WITH_CYCLES'
    return dict(case=i,dirs=ds,alpha=BOUNDS,cap=cap,status=status,selected=selected,census=report,cycle_cuts=cuts,seconds=time.monotonic()-t)

if __name__=='__main__':
    data=dict(status='PASSED',rows=controls())
    (HERE/'data/counter-controls.json').write_text(json.dumps(data,indent=2)+'\n');print(data,flush=True)
    for i in [3,2]:
        for cap in [24,25,26,27,28]:
            row=solve(i,cap)
            row['script_sha256_lf']=hashlib.sha256(Path(__file__).read_bytes().replace(b'\r\n',b'\n')).hexdigest()
            (HERE/f'data/independent-{i}-{cap}.json').write_text(json.dumps(row,indent=2)+'\n')
            print(i,cap,row['status'],row['census']['alpha'] if row['census'] else '',flush=True)
