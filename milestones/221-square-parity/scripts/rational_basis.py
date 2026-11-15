"""Recover an exact rational basis point and check all cycle inequalities."""
from pathlib import Path
from fractions import Fraction as Q
import hashlib, heapq, json, sys, time
H=Path(__file__).resolve().parents[1]; R=H.parents[1]
sys.path.insert(0,str(R/'work/solver_packages'))
from ortools.linear_solver import pywraplp
def sha(p): return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def save(p,x): p.write_text(json.dumps(x,indent=2)+'\n',encoding='utf-8')
def rat(q): return [q.numerator,q.denominator]
summaries=[]
for root in [0,78]:
    base=H/'data'/f'square-{root}'/'model.json'; m=json.loads(base.read_bytes())
    F=H/'data'/f'rational-{root}'; assert not F.exists(); F.mkdir()
    solver=pywraplp.Solver.CreateSolver('GLOP'); solver.SetNumThreads(1); solver.SetTimeLimit(45000)
    z=[solver.NumVar(0,1,n) for n in m['variables']]; cons=[]
    for row in m['rows']:
        c=solver.Constraint(row['rhs'] if row['sense']=='eq' else -solver.infinity(),row['rhs'])
        for i,a in row['terms']: c.SetCoefficient(z[i],a)
        cons.append(c)
    obj=solver.Objective()
    for i,a in enumerate(m['objective']): obj.SetCoefficient(z[i],a)
    obj.SetMaximization(); started=time.monotonic(); assert solver.Solve()==pywraplp.Solver.OPTIMAL
    fixed={}; unknown=[]
    for i,v in enumerate(z):
        status=v.basis_status()
        if status==solver.BASIC: unknown.append(i)
        else:
            assert status in [solver.AT_LOWER_BOUND,solver.AT_UPPER_BOUND]
            fixed[i]=Q(status==solver.AT_UPPER_BOUND)
    equations=[]
    for row,c in zip(m['rows'],cons):
        if c.basis_status()==solver.BASIC: continue
        coeff={i:Q(a) for i,a in row['terms'] if i not in fixed}
        rhs=Q(row['rhs'])-sum((a*fixed[i] for i,a in row['terms'] if i in fixed),Q())
        equations.append([coeff,rhs])
    save(F/'basis.json',{'variable_status':[v.basis_status() for v in z],
        'row_status':[c.basis_status() for c in cons],'basic_variable_count':len(unknown),
        'equation_count':len(equations),'native_objective':obj.Value(),'model_sha256':sha(base)})
    pivots=[]
    while equations:
        nonempty=[]
        for a,b in equations:
            if a: nonempty.append([a,b])
            else: assert b==0
        equations=nonempty
        if not equations: break
        pos=min(range(len(equations)),key=lambda k:len(equations[k][0]))
        a,b=equations.pop(pos); pivot=min(a,key=lambda j:sum(j in c for c,d in equations))
        scale=a.pop(pivot); a={j:q/scale for j,q in a.items()}; b/=scale
        for c,dummy in equations:
            if pivot not in c: continue
        for eq in equations:
            c,d=eq
            if pivot not in c: continue
            f=c.pop(pivot)
            for j,q in a.items():
                c[j]=c.get(j,Q())-f*q
                if not c[j]: del c[j]
            eq[1]=d-f*b
        pivots.append((pivot,a,b))
    assert len(pivots)==len(unknown),(len(pivots),len(unknown))
    values=fixed.copy()
    for pivot,a,b in reversed(pivots): values[pivot]=b-sum((q*values[j] for j,q in a.items()),Q())
    values=[values[i] for i in range(len(z))]
    assert all(0<=q<=1 for q in values)
    for row in m['rows']:
        lhs=sum((a*values[i] for i,a in row['terms']),Q())
        assert lhs==row['rhs'] if row['sense']=='eq' else lhs<=row['rhs'],row['name']
    objective=sum((a*q for a,q in zip(m['objective'],values)),Q())
    V=m['vertices']; ix={v:i for i,v in enumerate(V)}; N={v:[] for v in V}
    costs={v:1-values[ix[v]] for v in V}
    for u,v in m['edges']: N[u].append(v); N[v].append(u)
    potentials=[]; minimum=None
    for source,target in m['edges']:
        # Twice the edge length is cost(u)+cost(v), avoiding division by two.
        dist={source:Q()}; todo=[(Q(),source)]; settled=set()
        while todo:
            d,u=heapq.heappop(todo)
            if u in settled: continue
            settled.add(u)
            for v in N[u]:
                if {u,v}=={source,target} or v in settled: continue
                nd=d+costs[u]+costs[v]
                if v not in dist or nd<dist[v]: dist[v]=nd; heapq.heappush(todo,(nd,v))
        if target in dist:
            bound=(dist[target]+costs[source]+costs[target])/2
            minimum=bound if minimum is None else min(minimum,bound)
        else: bound=None
        # A finite potential on all vertices is a short exact certificate.
        # An unreachable component can be assigned the maximum reached value.
        cap=max(dist.values()); p={v:dist.get(v,cap) for v in V}
        assert p[source]==0
        assert all(abs(p[u]-p[v])<=costs[u]+costs[v] for u,v in m['edges'] if {u,v}!={source,target})
        potentials.append({'edge':[source,target],'distance':[rat(p[v]) for v in V],
            'target_reachable':target in dist,'cycle_lower_bound':rat(bound) if bound is not None else None})
    certificate={'model_sha256':sha(base),'source_sha256':sha(__file__),
        'values':[rat(q) for q in values],'objective':rat(objective),
        'minimum_cycle_cost':rat(minimum),'all_cycle_inequalities':minimum>=1,
        'potentials':potentials,'scope':'Exact rational point, not a Boolean path. Every saved row checked; edge-deleted distance potentials certify all simple cycle inequalities when their bounds are at least one.'}
    save(F/'primal-certificate.json',certificate)
    summary={'root':root,'objective':rat(objective),'objective_float':float(objective),
        'basic_variable_count':len(unknown),'minimum_cycle_cost':rat(minimum),'all_cycle_inequalities':minimum>=1,
        'maximum_denominator_bits':max(q.denominator.bit_length() for q in values),
        'seconds':time.monotonic()-started,'certificate_sha256':sha(F/'primal-certificate.json')}
    summaries.append(summary); save(H/'data/rational-summary.json',summaries); print(json.dumps(summary),flush=True)
