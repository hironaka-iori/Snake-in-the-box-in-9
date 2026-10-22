"""Find and exactly check a periodic obstruction to the CURRENT five-window cache.

This is an obstruction to these recorded numerical premises, not a snake.
It does not certify a minimum mean or a global snake bound.
"""
import ast,hashlib,itertools,json,subprocess,sys,time
from fractions import Fraction as F
from pathlib import Path
ROOT=Path(__file__).resolve().parents[3];HERE=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'work/solver_packages'))
import numpy as np
from ortools.linear_solver import pywraplp
sys.path.insert(0,str(ROOT/'milestones/27-empty-square-packing/scripts'))
from packing import cache,canon,key
REF='41797e38'
def git(*args):return subprocess.check_output(['git','-c',f'safe.directory={ROOT.as_posix()}',*args],cwd=ROOT)
def induced(ds):
    p=[0]
    for a in ds:p.append(p[-1]^(1<<a))
    return len(p)==len(set(p)) and all((x^p[j]).bit_count()!=1 for i,x in enumerate(p) for j in range(i+2,len(p)))
def load_functions():
    name='milestones/10-window-aggregate/scripts/refine.py'
    raw=git('show',f'{REF}:{name}').replace(b'\r\n',b'\n')
    # Only the already inspected graph algorithms are loaded; no oracle or solver startup.
    tree=ast.parse(raw);nodes=[n for n in tree.body if isinstance(n,ast.FunctionDef) and n.name in ('prune','howard')]
    ns={'np':np};exec(compile(ast.Module(body=nodes,type_ignores=[]),name,'exec'),ns)
    return ns,hashlib.sha256(raw).hexdigest()
def main():
    t=time.monotonic();ref=git('rev-parse',REF).decode().strip()
    raw=git('show',f'{REF}:milestones/10-window-aggregate/data/direction_certificates_r4c.json')
    idx=json.loads(raw);cases=idx['cases'];assert all(r['drat_trim_verified'] for r in cases)
    forbidden={key(r['dirs'],r['alpha']) for r in cases}
    lb,excluded,_=cache();forbidden|=excluded
    shapes=[()]
    for length in range(7):
        shapes=[c+(d,) for c in shapes for d in range(min(max(c,default=-1)+2,9)) if induced(c+(d,))]
    shapes=sorted(shapes);counts=list(itertools.product(range(1,7),repeat=4))
    states=[(c,a) for c in shapes for a in counts];sid={s:i for i,s in enumerate(states)}
    direction_edges={c:[(c+(d,),canon(c[1:]+(d,))) for d in range(min(max(c)+2,9)) if induced(c+(d,))] for c in shapes}
    U=[];V=[];A=[];B=[];DS=[]
    ranges={s:(s,s) if s<6 else (6,21) for s in range(1,7)}
    for u,(c,a) in enumerate(states):
        for ds,nc in direction_edges[c]:
            for s in range(1,7):
                al=a+(s,);ks=[key(ds[-(k+1):],tuple(ranges[z] for z in al[-k:])) for k in range(2,6)]
                if any(k in forbidden for k in ks):continue
                U.append(u);V.append(sid[(nc,al[1:])]);A.append(s);B.append(lb.get(ks[-1],0));DS.append(ds)
    U=np.array(U);V=np.array(V);A=np.array(A);B=np.array(B)
    ns,sourcehash=load_functions();keep=ns['prune'](len(states),U,V);ids=np.flatnonzero(keep)
    print('graph',len(states),len(ids),'seconds',round(time.monotonic()-t,1),flush=True)
    _,cyc=ns['howard'](len(states),U[ids],V[ids],120*A[ids]+B[ids]);edges=[int(ids[e]) for e in cyc]
    n=len(edges);assert n>=5
    for i,e in enumerate(edges):assert V[e]==U[edges[(i+1)%n]]
    bounds=[int(B[e]) for e in edges];alphas=[int(A[e]) for e in edges]
    # Minimize an admissible periodic share assignment; round UP, then verify every constraint exactly.
    solver=pywraplp.Solver.CreateSolver('GLOP');s=[solver.NumVar(0,solver.infinity(),str(j)) for j in range(n)]
    for i,b in enumerate(bounds):solver.Add(sum(s[(i-j)%n] for j in range(5))>=b)
    solver.Minimize(sum(s));assert solver.Solve()==solver.OPTIMAL
    fractional=[F(x.solution_value()).limit_denominator(100000) for x in s]
    shares=[max(0,-(-x.numerator//x.denominator)) for x in fractional]
    assert all(sum(shares[(i-j)%n] for j in range(5))>=b for i,b in enumerate(bounds))
    mean=F(24*sum(alphas)+sum(shares),24*n)
    records=[]
    for i,e in enumerate(edges):
        ds=DS[e];u=int(U[e]);v=int(V[e]);al=states[u][1]+(int(A[e]),)
        for k in range(2,6):assert key(ds[-(k+1):],tuple(ranges[z] for z in al[-k:])) not in forbidden
        records.append(dict(state=[list(states[u][0]),list(states[u][1])],next_state=[list(states[v][0]),list(states[v][1])],directions=list(ds),alpha=alphas[i],share=shares[i],five_window_bound=bounds[i],five_window_key=[list(key(ds[-6:],tuple(ranges[z] for z in al))[0]),[list(z) for z in key(ds[-6:],tuple(ranges[z] for z in al))[1]]]))
    out=dict(scope='Periodic feasible vector for the recorded five-window M12 inequalities and listed exclusions only; not a snake.',upstream_commit=ref,exclusion_index_sha256=hashlib.sha256(raw).hexdigest(),algorithm_sha256_lf=sourcehash,excluded_keys=len(forbidden),states=len(states),retained_edges=len(ids),period=n,charge_mean=str(mean),target_mean='19/4',below_target=mean<F(19,4),records=records,seconds=round(time.monotonic()-t,3))
    (HERE/'data/cache-obstruction.json').write_text(json.dumps(out,indent=2)+'\n')
    # Pin the exact exclusion keys, without copying the large certificate metadata.
    (HERE/'data/exclusion-keys.json').write_text(json.dumps([[list(d),[list(a) for a in al]] for d,al in sorted(forbidden)])+'\n')
    print(json.dumps({k:v for k,v in out.items() if k!='records'}),flush=True)
if __name__=='__main__':main()
