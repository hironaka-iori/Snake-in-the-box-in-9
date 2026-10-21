"""Exact checks of rational packing certificates on saved periodic window patterns.

The local lower bounds are collaborator solver results, NOT Lean certificates.
Only the packing deduction and the share loss identity are kernel checked here.
"""
import hashlib,itertools,json,random,sys
from fractions import Fraction as F
from pathlib import Path
ROOT=Path(__file__).resolve().parents[3]; HERE=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'work/solver_packages'))
from ortools.linear_solver import pywraplp

def canon(ds):
    names={}; out=[]
    for d in ds:
        if d not in names:names[d]=len(names)
        out.append(names[d])
    return tuple(out)
def key(ds,al):
    al=tuple(tuple(a) if isinstance(a,(list,tuple)) else (a,a) for a in al)
    return min((canon(ds),al),(canon(ds[::-1]),al[::-1]))

def cache():
    lb={}; excluded=set(); counts={}
    for fn in ['threshold_results.jsonl','ceiling_results.jsonl','probe_results.jsonl','refshare_results.jsonl']:
        rows=[json.loads(s) for s in (HERE/'upstream'/fn).read_text().splitlines() if s.strip()]
        counts[fn]=len(rows)
        for r in rows:
            if r.get('M',12)!=12:continue
            al=r.get('alpha') or [(6,21) if s=='6+' else (int(s),int(s)) for s in r['alpha_req'].split(',')]
            if len(r['dirs'])!=6:continue
            k=key(r['dirs'],al)
            if r.get('status')=='UNSAT_MODEL':excluded.add(k);continue
            b=(r['T'] if r['result']=='UNSAT' else 0) if 'result' in r else r.get('min_lower',0)
            lb[k]=max(lb.get(k,0),b)
    return lb,excluded,counts

def dp(bounds,n):
    D=[0]*(n+1); chosen=[[] for _ in D]
    for k in range(1,n+1):
        D[k]=D[k-1];chosen[k]=chosen[k-1]
        if k>=5 and D[k-5]+bounds[k-5]>D[k]:
            D[k]=D[k-5]+bounds[k-5];chosen[k]=chosen[k-5]+[k-5]
    used=[j for i in chosen[-1] for j in range(i,i+5)]
    assert len(set(used))==len(used) and all(j<n for j in used)
    assert D[-1]==sum(bounds[i] for i in chosen[-1])
    return D[-1],chosen[-1]

def controls():
    rng=random.Random(196); cases=0
    for n in range(5,17):
        for _ in range(20):
            b=[rng.randrange(30) for _ in range(n-4)]
            best=0
            for mask in range(1<<len(b)):
                indices=[i for i in range(len(b)) if mask>>i&1]
                if all(j-i>=5 for i,j in zip(indices,indices[1:])):
                    best=max(best,sum(b[i] for i in indices))
            assert dp(b,n)[0]==best;cases+=1
    return cases

def pack_cycle(bounds):
    n=len(bounds)
    assert n>=5
    windows=[{(i+j)%n for j in range(5)} for i in range(n)]
    solver=pywraplp.Solver.CreateSolver('GLOP')
    w=[solver.NumVar(0,solver.infinity(),str(i)) for i in range(n)]
    for v in range(n):solver.Add(sum(w[i] for i in range(n) if v in windows[i])<=1)
    solver.Maximize(sum(bounds[i]*w[i] for i in range(n)))
    assert solver.Solve()==solver.OPTIMAL
    weights=[F(x.solution_value()).limit_denominator(100000) for x in w]
    # These exact assertions, not the floating-point optimizer, certify the lower bound.
    assert all(x>=0 for x in weights)
    loads=[sum((weights[i] for i in range(n) if v in windows[i]),F(0)) for v in range(n)]
    assert all(x<=1 for x in loads)
    packed=sum((b*x for b,x in zip(bounds,weights)),F(0))
    uniform=F(sum(bounds),5)
    assert packed>=uniform
    return dict(uniform=str(uniform),packed=str(packed),gain=str(packed-uniform),
                weights=list(map(str,weights)),loads=list(map(str,loads)))

def main():
    lb,excluded,counts=cache(); out=[]
    for fn in ['aut_base.json','aut_pair_lo.json','aut_single_lo.json','aut_single_ub.json','aut_tri_lo.json']:
        r=json.loads((HERE/'upstream'/fn).read_text());syms=r['cycle_syms'];n=len(syms)
        if 'cycle_windows' not in r or any(len(ws[-1][1])!=5 for ws in r['cycle_windows']):
            out.append(dict(source=fn,status='five_centre_windows_not_saved'));continue
        keys=[key(*ws[-1]) for ws in r['cycle_windows']]
        assert len(keys)==n and all(len(k[1])==5 for k in keys)
        # Keys may be reversed by canonicalization. Check against the actual cyclic symbol window.
        for i,k in enumerate(keys):
            expected=tuple((min(syms[(i-4+j)%n],6),21 if syms[(i-4+j)%n]>=6 else syms[(i-4+j)%n]) for j in range(5))
            assert k[1] in (expected,expected[::-1])
        if any(k in excluded for k in keys):
            out.append(dict(source=fn,status='excluded_by_collaborator_model_result'));continue
        # bounds indexed by start, whereas saved windows are indexed by end.
        bounds=[lb.get(keys[(i+4)%n],0) for i in range(n)]
        if n<5:
            out.append(dict(source=fn,status='cycle_too_short_for_this_test'));continue
        p=pack_cycle(bounds)
        alpha=F(sum(syms),n)
        p.update(source=fn,status='conditional_on_solver_lower_bounds',period=n,bounds=bounds,
                 alpha_mean=str(alpha),uniform_charge_mean=str(alpha+F(p['uniform'])/(24*n)),
                 packed_charge_mean=str(alpha+F(p['packed'])/(24*n)))
        # A line of 100 periods independently checks an integral nonoverlapping selection.
        length=100*n
        value,starts=dp([bounds[i%n] for i in range(length-4)],length)
        p['line_dp_share_per_period']=str(F(value,100));p['line_dp_windows']=len(starts)
        out.append(p)
    report=dict(upstream_commit=json.loads((HERE/'data/provenance.json').read_text())['commit'],
                controls=controls(),cache_records=counts,distinct_five_window_bounds=len(lb),
                excluded_windows=len(excluded),cycles=out,
                warning='No new universal upper bound. Local lower bounds have not been replayed in Lean.')
    (HERE/'data/packing-results.json').write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps(report,indent=2))
if __name__=='__main__':main()
