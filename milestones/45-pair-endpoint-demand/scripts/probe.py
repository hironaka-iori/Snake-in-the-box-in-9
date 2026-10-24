"""Attempt to falsify endpoint proximity at the sharp pair-count boundary."""
from pathlib import Path
import itertools,json,sys,time
ROOT=Path(__file__).resolve().parents[3];HERE=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'milestones/29-overlapping-share-windows/scripts'))
from joint import TaggedEncoding,window,Cadical153,census
DS=[0,1,2,3,4,0,3,1];W=window(DS)
(HERE/'data').mkdir(parents=True,exist_ok=True)

def solve(name,centres,avoid_radius,ball_radius=4,cap=7,seconds=10):
    e=TaggedEncoding(W,[(0,21)]*7,radius=ball_radius)
    lits=[-e.var[W[j]^(1<<a)^(1<<b)] for j in [2,6] for a,b in itertools.combinations(range(9),2) if a not in (DS[j-1],DS[j]) and b not in (DS[j-1],DS[j])]
    e.atmost(lits,cap,('ends',))
    avoid={v for v in range(512) if any((v^c).bit_count()<=avoid_radius for c in centres)}
    endvars={v:k for k,(kind,v,*_) in e.meaning.items() if kind=='e'}
    assert avoid<=endvars.keys()
    for v in sorted(avoid):e.add([-endvars[v]],('avoid',v))
    t=time.monotonic();cuts=[];selected=None;path=None;report=None;status='UNKNOWN'
    with Cadical153(bootstrap_with=e.clauses) as solver:
        while time.monotonic()-t<seconds:
            solver.conf_budget(4000);ok=solver.solve_limited()
            if ok is None:continue
            if not ok:status='UNSAT';break
            model=solver.get_model();S={v for v in e.ball if model[e.var[v]-1]>0}
            report=census(S,9,W[1:-1]);report.pop('degree')
            if report['cycles']:
                for c in report['cycles']:cuts.append(c);solver.add_clause([-e.var[v] for v in c])
                continue
            selected=sorted(S);status='SAT'
            if ball_radius==9:
                neighbors=lambda v:[v^(1<<d) for d in range(9) if v^(1<<d) in S]
                ends=[v for v in S if len(neighbors(v))==1];assert len(ends)==2
                path=[min(ends)]
                while len(path)<len(S):
                    nxt=[v for v in neighbors(path[-1]) if len(path)==1 or v!=path[-2]]
                    assert len(nxt)==1;path.append(nxt[0])
                assert len(path)==len(set(path))
                assert all(((path[i]^path[j]).bit_count()==1)==(j==i+1) for i in range(len(path)) for j in range(i+1,len(path)))
                assert all(v not in avoid for v in ends)
            break
    out=dict(name=name,directions=DS,positions=[2,6],joint_cap=cap,avoid_centres=centres,avoid_radius=avoid_radius,ball_radius=ball_radius,
        avoid_vertices=sorted(avoid),status=status,selected=selected,vertex_sequence=path,census=report if selected else None,cycle_cuts=cuts,seconds=time.monotonic()-t,
        scope='Endpoint avoidance is an extra hypothesis. Solver UNSAT is not yet a theorem; local SAT is not a complete snake unless a full vertex sequence is returned.')
    (HERE/f'data/{name}.json').write_text(json.dumps(out,indent=2)+'\n')
    print(name,status,'counts',report['alpha'] if selected else None,'edges',len(path)-1 if path else None,'cuts',len(cuts),flush=True)
    return out

if __name__=='__main__':
    for radius in [1,2,3]:solve('pair-radius-'+str(radius),[W[2],W[6]],radius)
    solve('first-radius-2',[W[2]],2)
    solve('second-radius-2',[W[6]],2)
    for radius in [1,2,3]:solve('full-pair-radius-'+str(radius),[W[2],W[6]],radius,ball_radius=9,seconds=15)
