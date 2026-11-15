"""Strengthen saved edge relaxations by explicit valid cycle inequalities."""
from pathlib import Path
from fractions import Fraction
import hashlib,heapq,json,sys,time
H=Path(__file__).resolve().parents[1];R=H.parents[1]
sys.path.insert(0,str(R/'work/solver_packages'))
from ortools.linear_solver import pywraplp
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def save(p,x):p.write_text(json.dumps(x,indent=2)+'\n',encoding='utf-8')
all_reports=[]
for root in [0,78]:
    base=H/'data'/f'edge-{root}'/'model.json';model=json.loads(base.read_bytes())
    F=H/'data'/f'cycles-{root}';assert not F.exists();F.mkdir()
    V=model['vertices'];edges=model['edges'];N={v:[] for v in V}
    for u,v in edges:N[u].append(v);N[v].append(u)
    ix={v:i for i,v in enumerate(V)};rows=model['rows'];known={tuple(sorted(c)) for c in model['cycles']}
    solver=pywraplp.Solver.CreateSolver('GLOP');assert solver is not None
    solver.SetNumThreads(1);solver.SetTimeLimit(45000)
    z=[solver.NumVar(0,1,n) for n in model['variables']];constraints=[]
    def install(spec):
        c=solver.Constraint(spec['rhs'] if spec['sense']=='eq' else -solver.infinity(),spec['rhs'],spec['name'])
        for i,a in spec['terms']:c.SetCoefficient(z[i],a)
        constraints.append(c)
    for spec in rows:install(spec)
    obj=solver.Objective()
    for i,a in enumerate(model['objective']):obj.SetCoefficient(z[i],a)
    obj.SetMaximization();steps=[];added=[];started=time.monotonic()
    for iteration in range(41):
        status=solver.Solve();assert status==pywraplp.Solver.OPTIMAL
        values=[v.solution_value() for v in z];costs={v:max(0.0,1-values[ix[v]]) for v in V}
        violations={};minimum=1e100
        for source,target in edges:
            distance={source:0.0};previous={};todo=[(0.0,source)];settled=set()
            while todo:
                d,u=heapq.heappop(todo)
                if u in settled:continue
                settled.add(u)
                if u==target:break
                for v in N[u]:
                    if (u==source and v==target) or (u==target and v==source) or v in settled:continue
                    nd=d+(costs[u]+costs[v])/2
                    if nd<distance.get(v,float('inf'))-1e-12:
                        distance[v]=nd;previous[v]=u;heapq.heappush(todo,(nd,v))
            if target not in settled:continue
            path=[target]
            while path[-1]!=source:path.append(previous[path[-1]])
            path.reverse();assert len(path)>=4 and len(path)==len(set(path))
            assert all(v in N[u] for u,v in zip(path,path[1:]+path[:1]))
            cost=sum(costs[v] for v in path);minimum=min(minimum,cost);key=tuple(sorted(path))
            if cost<1-1e-8 and key not in known:
                violations[key]={'cycle':path,'cost':cost,'selected_sum':sum(values[ix[v]] for v in path)}
        entry={'iteration':iteration,'objective':obj.Value(),'violated_new_cycles':len(violations),
               'minimum_detected_cycle_cost':minimum,'constraints':len(rows)}
        steps.append(entry);print(json.dumps({'root':root,**entry}),flush=True)
        if not violations or iteration==40:break
        for key,witness in sorted(violations.items()):
            C=witness['cycle'];known.add(key)
            spec={'name':'separated_cycle_'+str(len(added)),'terms':[[ix[v],1] for v in sorted(C)],'sense':'le','rhs':len(C)-1}
            rows.append(spec);install(spec);added.append({'iteration':iteration,**witness,'row_index':len(rows)-1})
    model['base_model_sha256']=sha(base);model['separation_source_sha256']=sha(__file__)
    model['separated_cycles']=added;model['scope']+=' Saved added cycles are valid; floating-point separation is not an exact closure certificate.'
    save(F/'model.json',model)
    duals=[c.dual_value() for c in constraints];scale=10**6
    weights=[max(0,round(w*scale)) if spec['sense']=='le' else round(w*scale) for spec,w in zip(rows,duals)]
    residual=[scale*c for c in model['objective']];rhs=0
    for spec,w in zip(rows,weights):
        rhs+=spec['rhs']*w
        for i,a in spec['terms']:residual[i]-=a*w
    upper=rhs+sum(max(r,0) for r in residual);q=Fraction(upper,scale)
    save(F/'upper-certificate.json',{'scale':scale,'weights':weights,'residual':residual,'positive_residual':[max(r,0) for r in residual],
        'upper_numerator':upper,'upper_bound':[q.numerator,q.denominator],'model_sha256':sha(F/'model.json')})
    result={'root':root,'status':'OPTIMAL_NATIVE','objective':obj.Value(),'seconds':time.monotonic()-started,
        'steps':steps,'added_cycle_count':len(added),'values':values,'duals':duals,'exact_upper':[q.numerator,q.denominator],
        'model_sha256':sha(F/'model.json'),'solver_version':solver.SolverVersion(),
        'separation_limit':40,'no_new_violations_at_tolerance':not bool(violations)}
    save(F/'native-result.json',result)
    all_reports.append({k:v for k,v in result.items() if k not in ['values','duals','steps']})
    save(H/'data/cycle-summary.json',all_reports)
