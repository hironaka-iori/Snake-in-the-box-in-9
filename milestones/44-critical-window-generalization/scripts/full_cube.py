"""Seek complete snakes attaining the pair bound and testing shorter context."""
from probe import p,HERE
import itertools,json,time

def search(name,ds,positions,cap,seconds=20):
    W=p.window(ds);e=p.TaggedEncoding(W,[(0,21)]*(len(ds)-1),radius=9)
    assert len(e.ball)==512
    lits=[-e.var[W[j]^(1<<a)^(1<<b)] for j in positions
          for a,b in itertools.combinations(range(9),2)
          if a not in (ds[j-1],ds[j]) and b not in (ds[j-1],ds[j])]
    e.atmost(lits,cap,('ends',));cuts=[];status='UNKNOWN';path=None;t=time.monotonic()
    with p.Cadical153(bootstrap_with=e.clauses) as solver:
        while time.monotonic()-t<seconds:
            solver.conf_budget(3000);ok=solver.solve_limited()
            if ok is None:continue
            if not ok:status='UNSAT';break
            model=solver.get_model();S={v for v in e.ball if model[e.var[v]-1]>0}
            report=p.census(S,9,W[1:-1]);report.pop('degree')
            if report['cycles']:
                for c in report['cycles']:cuts.append(c);solver.add_clause([-e.var[v] for v in c])
                continue
            neighbors=lambda v:[v^(1<<j) for j in range(9) if v^(1<<j) in S]
            ends=[v for v in S if len(neighbors(v))==1];assert len(ends)==2
            path=[min(ends)]
            while len(path)<len(S):
                nxt=[v for v in neighbors(path[-1]) if len(path)==1 or v!=path[-2]]
                assert len(nxt)==1;path.append(nxt[0])
            assert len(set(path))==len(S)
            assert all(((path[i]^path[j]).bit_count()==1)==(j==i+1) for i in range(len(path)) for j in range(i+1,len(path)))
            if not any(path[r:r+len(W)]==W for r in range(len(path)-len(W)+1)):path=path[::-1]
            start=next(r for r in range(len(path)-len(W)+1) if path[r:r+len(W)]==W)
            assert sum(report['alpha'][j-1] for j in positions)<=cap
            status='SAT';break
    out=dict(name=name,directions=ds,positions=positions,cap=cap,status=status,seconds=time.monotonic()-t,cycle_cuts=cuts,
        vertex_sequence=path,window_start=start if path else None,census=report if path else None,
        scope='A returned complete snake is independently pair checked; solver failures are not certified exclusions.')
    (HERE/f'data/{name}.json').write_text(json.dumps(out,indent=2)+'\n')
    print(name,status,'length',len(path)-1 if path else None,'cuts',len(cuts),flush=True)

if __name__=='__main__':
    search('full-sharp-seven',[0,1,2,3,4,0,3,1],[2,6],7)
    search('full-short-six',[0,1,2,3,4,2],[1,5],6)
