"""Choose a small pending-proof set whose removal makes the restricted graph acyclic."""
from pathlib import Path
import json,sys,collections
HERE=Path(__file__).resolve().parents[1];ROOT=HERE.parents[1]
sys.path.insert(0,str(ROOT/'work/solver_packages'))
from ortools.sat.python import cp_model
g=json.loads((ROOT/'milestones/64-neighbour-choice-share/data/analysis.json').read_text())
summary=json.loads((HERE/'data/summary.json').read_text());candidates=set(summary['excluded_candidates'])
model=cp_model.CpModel();rank=[model.NewIntVar(0,g['states']-1,f'r{i}') for i in range(g['states'])]
ban={i:model.NewBoolVar(f'ban{i}') for i in candidates};cost={}
for i,e in enumerate(g['edges']):
    c=model.Add(rank[e['v']]>=rank[e['u']]+1)
    if i in ban:
        c.OnlyEnforceIf(ban[i].Not())
        r=json.loads((HERE/f'data/cases/e{i:03d}.json').read_text())
        cost[i]=len(r['branches'])+sum(len(b['trace']) for b in r['branches'])
model.Minimize(sum(cost[i]*ban[i] for i in ban))
solver=cp_model.CpSolver();solver.parameters.max_time_in_seconds=20;solver.parameters.num_search_workers=2
status=solver.Solve(model);assert status in [cp_model.OPTIMAL,cp_model.FEASIBLE]
selected=sorted(i for i in ban if solver.Value(ban[i]));ranks=[solver.Value(r) for r in rank]
assert all(ranks[e['v']]>ranks[e['u']] for i,e in enumerate(g['edges']) if i not in selected)
out=dict(status=solver.StatusName(status),selected=selected,cost=sum(cost[i] for i in selected),ranks=ranks,
    selected_costs={i:cost[i] for i in selected},scope='Acyclicity after removal is verified, but each selected exclusion remains an unproved count-conditioned candidate. No actual snake exclusion or global bound.')
(HERE/'data/selected-exclusions.json').write_text(json.dumps(out,indent=2)+'\n');print({k:v for k,v in out.items() if k!='ranks'})
