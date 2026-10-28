"""Numerical lower bound for ambiguous empty squares; exact dual replay pending."""
from pathlib import Path
import itertools,json,sys,time
HERE=Path(__file__).resolve().parents[1];ROOT=HERE.parents[1]
sys.path.insert(0,str(ROOT/'work/solver_packages'))
from ortools.linear_solver import pywraplp
NB=[{x^(1<<d) for d in range(9)} for x in range(512)]
FACES=[];INC=[[] for _ in range(512)]
for a,b in itertools.combinations(range(9),2):
    mask=(1<<a)|(1<<b)
    for x in range(512):
        if x&mask:continue
        f=(x,x|(1<<a),x|(1<<b),x|mask);FACES.append(f)
        for q in f:INC[q].append(f)
def solve(case,branch,export=None):
    S=set(branch['selected']);D=set(branch['absent']);C=case['vertices'][4:9]
    model=pywraplp.Solver.CreateSolver('GLOP');model.SetTimeLimit(10000)
    x=[model.NumVar(1 if v in S else 0,0 if v in D else 1,f'x{v}') for v in range(512)]
    for v in range(512):
        model.Add(sum(x[q] for q in NB[v])+7*x[v]<=9)
        model.Add(sum(x[q] for q in NB[v])-x[v]>=0)
    for f in FACES:model.Add(sum(x[q] for q in f)<=3)
    for c in case['constraints']:
        model.Add(sum(x[q] for q in c['corners'])>=21-c['hi'])
        model.Add(sum(x[q] for q in c['corners'])<=21-c['lo'])
    weights={}
    for c in C:
        for q in NB[c]:
            degree=len(NB[q]-D);assert degree>0
            k=12//degree
            for f in INC[q]:
                if not(set(f)&S):weights[f]=weights.get(f,0)+k
    objective=model.Objective()
    for i,(f,w) in enumerate(weights.items()):
        e=model.NumVar(0,1,f'e{i}')
        model.Add(e+sum(x[q] for q in f)>=1)
        objective.SetCoefficient(e,w)
    objective.SetMinimization();status=model.Solve()
    if export is not None and status==model.OPTIMAL:
        variables=model.variables()
        rows=[]
        for row in model.constraints():
            dual=row.dual_value()
            if abs(dual)<1e-9:continue
            rows.append(dict(name=row.name(),dual=dual,lb=row.lb() if row.lb()>-1e100 else None,
                ub=row.ub() if row.ub()<1e100 else None,
                terms=[[j,row.GetCoefficient(v)] for j,v in enumerate(variables) if row.GetCoefficient(v)]))
        payload=dict(edge=case['edge'],objective=objective.Value(),rows=rows,
            variables=[dict(name=v.name(),lb=v.lb(),ub=v.ub(),reduced=v.reduced_cost(),value=v.solution_value(),cost=objective.GetCoefficient(v)) for v in variables],
            faces=[dict(vertices=f,weight=w) for f,w in weights.items()])
        Path(export).write_text(json.dumps(payload,indent=2)+'\n')
    return dict(status={model.OPTIMAL:'OPTIMAL',model.FEASIBLE:'FEASIBLE',model.INFEASIBLE:'INFEASIBLE'}.get(status,str(status)),
                objective=objective.Value() if status==model.OPTIMAL else None,
                variables=model.NumVariables(),constraints=model.NumConstraints())
if __name__=='__main__':
    selected=[int(x) for x in sys.argv[1:]] or [0,1,7,10,19,26,36,41]
    results=[]
    for i in selected:
        case=json.loads((HERE/f'data/cases/e{i:02d}.json').read_text());trial=case['trials'][case['chosen']]
        values=[];start=time.monotonic()
        for j,b in enumerate(trial['branches']):
            if b['status']!='CLOSED':continue
            value=dict(branch=j,**solve(case,b,HERE/f'data/dual-e{i:02d}-b{j:02d}.json' if i==7 else None));values.append(value)
        all_done=all(v['status'] in ['OPTIMAL','INFEASIBLE'] for v in values)
        feasible=[v['objective'] for v in values if v['status']=='OPTIMAL']
        result=dict(edge=i,lower=min(feasible) if feasible and all_done else None,branches=values,seconds=time.monotonic()-start,
                    scope='Floating-point relaxation only. Neither infeasibility nor a positive bound is certified until exact dual and deduction checks pass.')
        results.append(result);(HERE/'data/lp-probe.json').write_text(json.dumps(results,indent=2)+'\n')
        print({k:v for k,v in result.items() if k!='branches'},flush=True)
