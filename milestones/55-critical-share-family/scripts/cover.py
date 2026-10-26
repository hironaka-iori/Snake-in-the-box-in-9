"""Find a smallest family of proposed share rules meeting every current minimum cycle."""
from pathlib import Path
import itertools,json,sys
HERE=Path(__file__).resolve().parents[1];ROOT=HERE.parents[1]
sys.path.insert(0,str(ROOT/'work/solver_packages'))
from ortools.sat.python import cp_model

def find_cycle(edges,chosen):
    adj={}
    for i,e in enumerate(edges):
        if e['window'] in chosen:continue
        adj.setdefault(e['u'],[]).append((i,e['v']));adj.setdefault(e['v'],[])
    color={};parent={}
    for root in adj:
        if color.get(root,0):continue
        color[root]=1;stack=[(root,iter(adj[root]))]
        while stack:
            u,children=stack[-1];entry=next(children,None)
            if entry is None:color[u]=2;stack.pop();continue
            edge,v=entry
            if color.get(v,0)==1:
                cycle=[edge];x=u
                while x!=v:
                    pe=parent[x];cycle.append(pe);x=edges[pe]['u']
                return cycle[::-1]
            if not color.get(v,0):
                parent[v]=edge;color[v]=1;stack.append((v,iter(adj[v])))
    return None

def solve(edges,eligible):
    md=cp_model.CpModel();x={i:md.new_bool_var(f'rule{i}') for i in eligible}
    md.minimize(sum(x.values()));constraints=[]
    while True:
        solver=cp_model.CpSolver();solver.parameters.num_search_workers=1
        status=solver.solve(md)
        assert status==cp_model.OPTIMAL
        chosen={i for i,var in x.items() if solver.value(var)}
        cycle=find_cycle(edges,chosen)
        if cycle is None:break
        candidates=sorted({edges[e]['window'] for e in cycle}&set(eligible))
        if not candidates:
            return dict(status='UNCOVERABLE_WITH_CURRENT_CANDIDATES',uncovered_cycle=cycle)
        md.add(sum(x[i] for i in candidates)>=1);constraints.append(dict(cycle=cycle,candidates=candidates))
    # An independent exhaustive search checks minimal cardinality for this small family.
    checked=0
    for size in range(len(chosen)):
        for subset in itertools.combinations(eligible,size):
            assert find_cycle(edges,set(subset)) is not None,subset
            checked+=1
    return dict(status='MINIMUM_FINITE_CYCLE_COVER',selected=sorted(chosen),cardinality=len(chosen),
        independent_smaller_subsets_checked=checked,cycle_constraints=constraints)

if __name__=='__main__':
    windows=json.loads((HERE/'data/windows.json').read_text());eligible=[];ordinary=[]
    for i,row in enumerate(windows):
        control=json.loads((HERE/f'data/controls/w{i:02d}.json').read_text())
        screen=json.loads((HERE/f'data/screen/w{i:02d}.json').read_text())
        if screen['status']=='INFEASIBLE':
            assert control['status']=='SAT';eligible.append(i)
        if control['status']=='UNSAT':ordinary.append(i)
    edges=json.loads((HERE/'data/critical-edges.json').read_text())
    out=dict(eligible=eligible,ordinary_unsat=ordinary,share_only=solve(edges,eligible),
        with_observed_count_exclusions=solve([e for e in edges if e['window'] not in ordinary],eligible),
        scope='Exact cycle-cover optimization on the conditional critical graph. Share candidates and additional count exclusions are numerical; a cover is not a global bound.')
    (HERE/'data/cycle-cover.json').write_text(json.dumps(out,indent=2)+'\n')
    print({k:v for k,v in out.items() if k!='scope'},flush=True)
