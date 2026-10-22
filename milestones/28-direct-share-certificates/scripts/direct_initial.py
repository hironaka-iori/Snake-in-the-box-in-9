"""Independent CP-SAT radius-four share model, with exact quotient variables.

No SAT encoder, unary counter, or reported upstream witness value is reused.
INFEASIBLE remains an unchecked solver result, not a Lean refutation.
"""
import argparse,collections,hashlib,itertools,json,sys,time
from pathlib import Path
ROOT=Path(__file__).resolve().parents[3];HERE=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'work/solver_packages'))
from ortools.sat.python import cp_model

def window(dirs):
    w=[0]
    for a in dirs:w.append(w[-1]^(1<<a))
    return w

def model(n,dirs,bounds,radius=4,M=12,cap=None,fixed=None):
    win=window(dirs);centres=win[1:-1]
    B={v for v in range(1<<n) if min((v^c).bit_count() for c in centres)<=radius}
    md=cp_model.CpModel(); x={v:md.new_bool_var(f'x{v}') for v in sorted(B)}
    for v in win:md.add(x[v]==1)
    if fixed is not None:
        for v in B:md.add(x[v]==int(v in fixed))
    endpoints=[]
    for v in sorted(B):
        ns=[x[v^(1<<a)] for a in range(n) if (v^(1<<a)) in B]
        md.add(sum(ns)<=2).only_enforce_if(x[v])
        if len(ns)==n:
            e=md.new_bool_var(f'end{v}');endpoints.append(e)
            md.add(e<=x[v])
            md.add(sum(ns)==2-e).only_enforce_if(x[v])
    md.add(sum(endpoints)<=2)
    empties={}
    def empty(sq):
        k=tuple(sorted(sq))
        if k not in empties:
            z=md.new_bool_var('empty'+','.join(map(str,k)));empties[k]=z
            md.add(sum(x[v] for v in k)==0).only_enforce_if(z)
            md.add(sum(x[v] for v in k)>=1).only_enforce_if(z.Not())
        return empties[k]
    for c,(lo,hi) in zip(centres,bounds):
        single=[]
        for a,b in itertools.combinations(range(n),2):
            k=[c^(1<<a),c^(1<<b),c^(1<<a)^(1<<b)]
            assert set(k)<=B
            z=md.new_bool_var(f'alpha{c}_{a}_{b}')
            md.add(sum(x[v] for v in k)==0).only_enforce_if(z)
            md.add(sum(x[v] for v in k)>=1).only_enforce_if(z.Not())
            single.append(z)
        md.add(sum(single)>=lo);md.add(sum(single)<=hi)
    # Share terms for path neighbors vanish; all other neighbors are unselected.
    multiplicity=collections.Counter()
    for i,c in enumerate(centres,1):
        for a in range(n):
            q=c^(1<<a)
            if q not in (win[i-1],win[i+1]):multiplicity[q]+=1
    quotient={}
    for q in sorted(multiplicity):
        ns=[q^(1<<a) for a in range(n)];assert set(ns)<=B
        d=md.new_int_var(1,n,f'd{q}');md.add(d==sum(x[v] for v in ns))
        es=[]
        for a,b in itertools.combinations(range(n),2):
            sq=[q,q^(1<<a),q^(1<<b),q^(1<<a)^(1<<b)]
            assert set(sq)<=B
            es.append(empty(sq))
        e=md.new_int_var(0,n*(n-1)//2,f'e{q}');md.add(e==sum(es))
        u=md.new_int_var(0,M*n*(n-1)//2,f'u{q}');quotient[q]=u
        # All pairs are included: no additional unproved geometric cutoff.
        md.add_allowed_assignments([e,d,u],[(ee,dd,M*ee//dd) for dd in range(1,n+1) for ee in range(n*(n-1)//2+1)])
    total=sum(mult*quotient[q] for q,mult in multiplicity.items())
    if cap is not None:md.add(total<=cap)
    # Cheap sound cycle cuts, followed by all-length cycle separation during search.
    cuts=set()
    for v in sorted(B):
        for a,b in itertools.combinations(range(n),2):
            sq=frozenset((v,v^(1<<a),v^(1<<b),v^(1<<a)^(1<<b)))
            if sq<=B and sq not in cuts:
                md.add(sum(x[w] for w in sq)<=3);cuts.add(sq)
    return md,x,total,win,B,cuts

def census(S,n,centres,M=12):
    pairs=list(itertools.combinations(range(n),2))
    deg={q:sum((q^(1<<a)) in S for a in range(n)) for q in range(1<<n)}
    e={q:sum(not any(w in S for w in (q,q^(1<<a),q^(1<<b),q^(1<<a)^(1<<b))) for a,b in pairs) for q in range(1<<n)}
    alpha=[sum(not any(w in S for w in (c^(1<<a),c^(1<<b),c^(1<<a)^(1<<b))) for a,b in pairs) for c in centres]
    share=[sum(M*e[q]//deg[q] for a in range(n) if deg[q:=c^(1<<a)]) for c in centres]
    unseen=set(S);cycles=[]
    while unseen:
        stack=[next(iter(unseen))];comp=[]
        while stack:
            v=stack.pop()
            if v not in unseen:continue
            unseen.remove(v);comp.append(v)
            stack.extend(v^(1<<a) for a in range(n) if (v^(1<<a)) in unseen)
        if all(deg[v]==2 for v in comp):cycles.append(sorted(comp))
    return dict(alpha=alpha,share=share,total_share=sum(share),cycles=cycles,degree=deg)

def solve(case,seconds=30,fixed=None):
    t=time.monotonic();n=case.get('dimension',9)
    md,x,total,win,B,cuts=model(n,case['dirs'],case['alpha'],case.get('radius',4),12,case.get('cap'),fixed)
    initial=len(cuts);iterations=[];out=dict(case)
    out.update(model_build_seconds=round(time.monotonic()-t,3),ball_vertices=len(B),variables=len(md.proto.variables),constraints=len(md.proto.constraints))
    deadline=time.monotonic()+seconds
    while time.monotonic()<deadline:
        solver=cp_model.CpSolver();solver.parameters.max_time_in_seconds=max(.01,deadline-time.monotonic())
        solver.parameters.num_search_workers=2;solver.parameters.random_seed=196
        status=solver.solve(md);name=solver.status_name(status)
        iterations.append(dict(status=name,seconds=solver.wall_time,branches=solver.num_branches,conflicts=solver.num_conflicts))
        if status not in (cp_model.OPTIMAL,cp_model.FEASIBLE):out['status']=name;break
        S={v for v in B if solver.value(x[v])};c=census(S,n,win[1:-1]);deg=c.pop('degree')
        assert all(deg[v]<=2 for v in S)
        assert c['total_share']==solver.value(total)
        assert all(lo<=a<=hi for a,(lo,hi) in zip(c['alpha'],case['alpha']))
        if case.get('cap') is not None:assert c['total_share']<=case['cap']
        if not c['cycles']:
            out.update(status='FEASIBLE',selected=sorted(S),census=c);break
        for cc in c['cycles']:
            key=frozenset(cc);assert key not in cuts;cuts.add(key)
            md.add(sum(x[v] for v in cc)<=len(cc)-1)
    else:out['status']='TIME_LIMIT'
    out.update(iterations=iterations,additional_cycle_cuts=len(cuts)-initial,elapsed_seconds=round(time.monotonic()-t,3))
    return out

CASES=[
 dict(name='share163',dirs=[0,1,2,3,0,4],alpha=[[4,4],[6,21],[2,2],[6,21],[4,4]],cap=162),
 dict(name='share301',dirs=[0,1,2,3,0,4],alpha=[[2,2],[6,21],[2,2],[2,2],[6,21]],cap=300),
 dict(name='share245',dirs=[0,1,2,3,0,1],alpha=[[3,3],[2,2],[6,21],[3,3],[3,3]],cap=244),
 dict(name='pair10',dirs=[0,1,2],alpha=[[2,2],[2,2]],cap=9),
]
def main():
    ap=argparse.ArgumentParser();ap.add_argument('--seconds',type=float,default=30);ap.add_argument('--case',type=int);args=ap.parse_args()
    cases=CASES if args.case is None else [CASES[args.case]]
    for case in cases:
        row=solve(case,args.seconds);row['script_sha256_lf']=hashlib.sha256(Path(__file__).read_bytes().replace(b'\r\n',b'\n')).hexdigest()
        (HERE/'data'/f"{case['name']}.json").write_text(json.dumps(row,indent=2)+'\n')
        print(json.dumps({k:v for k,v in row.items() if k not in ('selected','iterations')}),flush=True)
if __name__=='__main__':main()
