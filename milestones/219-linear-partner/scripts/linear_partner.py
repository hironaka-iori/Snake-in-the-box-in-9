"""Solve necessary LP relaxations and construct exact upper-bound candidates."""
from pathlib import Path
from fractions import Fraction
import hashlib, json, sys, time
H=Path(__file__).resolve().parents[1]; R=H.parents[1]
sys.path.insert(0,str(R/'work/solver_packages'))
import ortools
from ortools.linear_solver import pywraplp

def sha(p): return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def save(p,d): p.write_text(json.dumps(d,indent=2)+'\n',encoding='utf-8')
def rat(q): return [q.numerator,q.denominator]

seed=json.loads((H/'data/seed98.json').read_bytes())['vertex_sequence']
graphs=json.loads((H/'data/complement-graph.json').read_bytes())
assert graphs['sha256']==sha(H/'data/seed98.json')
summaries=[]
for root in [0,78]:
    V=sorted(set(range(256))-(set(seed)-{root})); S=set(V)
    N={v:sorted(v^(1<<k) for k in range(8) if v^(1<<k) in S) for v in V}
    even=[v for v in V if v.bit_count()%2==0]; odd=[v for v in V if v.bit_count()%2==1]
    edges=[(u,v) for u in V for v in N[u] if u<v]
    graph=next(g for g in graphs['reports'] if g['root']==root)
    assert graph['allowed_vertices']==V and len(V)==158 and len(edges)==337
    cycles=graph['coordinate_squares']+graph['three_cube_induced_six_cycles']
    for cycle in cycles:
        assert len(set(cycle))==len(cycle)>=3 and set(cycle)<=S
        assert all(len(set(N[v])&set(cycle))==2 for v in cycle)
    for form in ['vertex','edge']:
        F=H/'data'/f'{form}-{root}'; assert not F.exists(); F.mkdir()
        names=[f'x{v}' for v in V]+[f'e{v}' for v in odd]
        ix={v:i for i,v in enumerate(V)}; ie={v:len(V)+i for i,v in enumerate(odd)}
        iy={}
        if form=='edge':
            for u,v in edges: iy[u,v]=len(names); names.append(f'y{u}_{v}')
        rows=[]
        def row(name,terms,sense,rhs):
            combined={}
            for i,c in terms: combined[i]=combined.get(i,0)+c
            rows.append({'name':name,'terms':[[i,c] for i,c in sorted(combined.items()) if c],
                         'sense':sense,'rhs':rhs})
        row('root_selected',[(ix[root],1)],'eq',1)
        row('root_degree',[(ix[w],1) for w in N[root]],'eq',1)
        row('one_free_endpoint',[(ie[v],1) for v in odd],'eq',1)
        row('parity_balance',[(ix[v],1 if v in even else -1) for v in V],'eq',0)
        for v in V:
            if v in ie: row(f'endpoint_selected_{v}',[(ie[v],1),(ix[v],-1)],'le',0)
            if v==root: continue
            ep=[(ie[v],1)] if v in ie else []
            row(f'degree_lower_{v}',[(ix[v],2)]+[(ix[w],-1) for w in N[v]]+[(i,-c) for i,c in ep],'le',0)
            row(f'degree_upper_{v}',[(ix[v],len(N[v])-2)]+[(ix[w],1) for w in N[v]]+ep,'le',len(N[v]))
        for i,C in enumerate(cycles): row(f'cycle_{i}',[(ix[v],1) for v in C],'le',len(C)-1)
        if form=='edge':
            for u,v in edges:
                y=iy[u,v]
                row(f'edge_le_left_{u}_{v}',[(y,1),(ix[u],-1)],'le',0)
                row(f'edge_le_right_{u}_{v}',[(y,1),(ix[v],-1)],'le',0)
                row(f'edge_ge_both_{u}_{v}',[(ix[u],1),(ix[v],1),(y,-1)],'le',1)
            for v in V:
                terms=[(iy[min(v,w),max(v,w)],1) for w in N[v]]
                if v==root: row('edge_root_degree',terms,'eq',1)
                else: row(f'edge_degree_{v}',terms+[(ix[v],-2)]+([(ie[v],1)] if v in ie else []),'eq',0)
        objective=[1 if i<len(V) else 0 for i in range(len(names))]
        model={'root':root,'form':form,'variables':names,'lower':[0]*len(names),'upper':[1]*len(names),
               'objective':objective,'rows':rows,'vertices':V,'edges':edges,'cycles':cycles,
               'source_sha256':sha(__file__),'seed_sha256':sha(H/'data/seed98.json'),
               'graph_sha256':sha(H/'data/complement-graph.json'),
               'scope':'Necessary relaxation of arbitrary odd-edge rooted partners of one fixed98-edge parent. No connectivity or integrality claim.'}
        save(F/'model.json',model)
        solver=pywraplp.Solver.CreateSolver('GLOP'); assert solver is not None
        solver.SetNumThreads(1); solver.SetTimeLimit(45000)
        z=[solver.NumVar(0,1,n) for n in names]; constraints=[]
        for spec in rows:
            c=solver.Constraint(spec['rhs'] if spec['sense']=='eq' else -solver.infinity(),spec['rhs'],spec['name'])
            for i,a in spec['terms']: c.SetCoefficient(z[i],a)
            constraints.append(c)
        obj=solver.Objective()
        for i,c in enumerate(objective): obj.SetCoefficient(z[i],c)
        obj.SetMaximization()
        started=time.monotonic(); status=solver.Solve(); seconds=time.monotonic()-started
        assert status==pywraplp.Solver.OPTIMAL, 'Preserve any nonoptimal result before using this script further.'
        values=[v.solution_value() for v in z]
        duals=[c.dual_value() for c in constraints]
        scale=10**6
        weights=[max(0,round(w*scale)) if spec['sense']=='le' else round(w*scale) for spec,w in zip(rows,duals)]
        residual=[scale*c for c in objective]
        rhs=0
        for spec,w in zip(rows,weights):
            rhs+=spec['rhs']*w
            for i,a in spec['terms']: residual[i]-=a*w
        upper_numerator=rhs+sum(max(r,0) for r in residual)
        bound=Fraction(upper_numerator,scale)
        certificate={'scale':scale,'weights':weights,'residual':residual,'positive_residual':[max(r,0) for r in residual],
                     'upper_numerator':upper_numerator,'upper_bound':rat(bound),'model_sha256':sha(F/'model.json'),
                     'argument':'Multiply each <= row by its nonnegative weight and each equality by its signed weight; use variable bounds0<=z<=1 for the residual. No LP optimality assumption is required.'}
        save(F/'upper-certificate.json',certificate)
        exact=None
        for denominator in [100,1000,10000,1000000,1000000000]:
            candidate=[Fraction(x).limit_denominator(denominator) for x in values]
            if not all(0<=x<=1 for x in candidate): continue
            ok=True
            for spec in rows:
                lhs=sum((a*candidate[i] for i,a in spec['terms']),Fraction())
                if not (lhs==spec['rhs'] if spec['sense']=='eq' else lhs<=spec['rhs']): ok=False; break
            if ok:
                exact=candidate; break
        native={'status':'OPTIMAL_NATIVE','root':root,'form':form,'seconds':seconds,'objective':obj.Value(),
                'values':values,'duals':duals,'ortools_version':ortools.__version__,'solver_version':solver.SolverVersion(),
                'iterations':solver.iterations(),'model_sha256':sha(F/'model.json'),
                'exact_upper':rat(bound),'exact_primal_reconstruction':exact is not None}
        if exact is not None:
            value=sum(exact[:len(V)],Fraction())
            save(F/'primal-certificate.json',{'values':[rat(q) for q in exact],'objective':rat(value),
                 'model_sha256':sha(F/'model.json'),'scope':'Exact rational feasibility checked against every saved row; not a Boolean path.'})
            native['exact_primal_objective']=rat(value)
        save(F/'native-result.json',native)
        summary={k:v for k,v in native.items() if k not in ['values','duals']}
        summary.update(variables=len(names),constraints=len(rows),upper_below_94=bound<94)
        summaries.append(summary); save(H/'data/lp-summary.json',summaries)
        print(json.dumps(summary),flush=True)
