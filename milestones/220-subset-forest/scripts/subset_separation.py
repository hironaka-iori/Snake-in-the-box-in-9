"""Separate induced-forest subset inequalities in the fixed-parent LPs."""
from pathlib import Path
from fractions import Fraction as Q
from math import lcm
import hashlib,json,sys,time
H=Path(__file__).resolve().parents[1];R=H.parents[1];P=H.parent/'219-linear-partner'
sys.path.insert(0,str(R/'work/solver_packages'))
from ortools.linear_solver import pywraplp
from ortools.graph.python import max_flow
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def save(p,x):p.write_text(json.dumps(x,indent=2)+'\n',encoding='utf-8')
def rat(q):return [q.numerator,q.denominator]
summary=[]
for root in [0,78]:
    base=P/'data'/f'edge-{root}'/'model.json';model=json.loads(base.read_bytes())
    F=H/'data'/f'forest-{root}';assert not F.exists();F.mkdir()
    V=model['vertices'];edges=model['edges'];names={n:i for i,n in enumerate(model['variables'])}
    ix={v:names[f'x{v}'] for v in V};ie={v:names[f'e{v}'] for v in V if f'e{v}' in names}
    iy={(u,v):names[f'y{u}_{v}'] for u,v in edges};pos={v:i for i,v in enumerate(V)};sink=len(V)
    arcs=[(u,v,iy[u,v]) for u,v in edges]+[(v,u,iy[u,v]) for u,v in edges]
    def flows(values,scale):
        caps=[int(values[i]*scale) for u,v,i in arcs]
        endpoints={v:scale if v==root else int(values[ie[v]]*scale) if v in ie else 0 for v in V}
        assert all(c>=0 for c in caps) and all(c>=0 for c in endpoints.values())
        assert sum(caps)+sum(endpoints.values())<2**62
        net=max_flow.SimpleMaxFlow()
        for (u,v,i),cap in zip(arcs,caps):net.add_arc_with_capacity(pos[u],pos[v],cap)
        for v in V:net.add_arc_with_capacity(pos[v],sink,endpoints[v])
        result=[]
        for v in V:
            if values[ix[v]]==0:continue
            status=net.solve(pos[v],sink);assert status==net.OPTIMAL
            U=sorted(V[j] for j in net.get_source_side_min_cut());assert v in U
            result.append((v,U,net.optimal_flow()))
        return result
    initial=[]
    for pointname in ['primal','target94']:
        p=P/'data'/f'rational-{root}'/(pointname+'-certificate.json');a=json.loads(p.read_bytes())
        values=[Q(*q) for q in a['values']];D=lcm(*(q.denominator for q in values))
        violated=[]
        for v,U,flow in flows(values,D):
            S=set(U);X=sum((values[ix[u]] for u in U),Q())
            Y=sum((values[iy[u,w]] for u,w in edges if u in S and w in S),Q())
            violation=Y-X+values[ix[v]]
            E=sum((Q(1) if u==root else values[ie[u]] if u in ie else Q() for u in U),Q())
            B=sum((values[iy[u,w]] for u,w in edges if (u in S)!=(w in S)),Q())
            assert Q(flow,D)==B+E and 2*violation==2*values[ix[v]]-B-E
            if violation>0:violated.append({'vertex':v,'subset':U,'violation':rat(violation),'cut_value':rat(B+E)})
        record={'point':pointname,'source_sha256':sha(p),'scale':D,'violated_witnesses':violated,
            'positive_count':len(violated),'largest_violation':rat(max((Q(*a['violation']) for a in violated),default=Q()))}
        initial.append(record);print(json.dumps({'root':root,'point':pointname,'violated_subset_count':len(violated),'scale_bits':D.bit_length(),'largest_violation':record['largest_violation']}),flush=True)
    save(F/'initial-separation.json',initial)
    rows=model['rows'];solver=pywraplp.Solver.CreateSolver('GLOP');solver.SetNumThreads(1);solver.SetTimeLimit(45000)
    z=[solver.NumVar(0,1,n) for n in model['variables']];constraints=[]
    def install(row):
        c=solver.Constraint(row['rhs'] if row['sense']=='eq' else -solver.infinity(),row['rhs'],row['name'])
        for i,a in row['terms']:c.SetCoefficient(z[i],a)
        constraints.append(c)
    for row in rows:install(row)
    obj=solver.Objective()
    for i,a in enumerate(model['objective']):obj.SetCoefficient(z[i],a)
    obj.SetMaximization();added=[];known=set();steps=[];started=time.monotonic()
    for iteration in range(61):
        assert solver.Solve()==solver.OPTIMAL
        values=[v.solution_value() for v in z];rounded=[Q(round(max(0,min(1,v))*10**8),10**8) for v in values]
        candidates=[];maximum=0
        for v,U,flow in flows(rounded,10**8):
            S=set(U);terms={ix[u]:-1 for u in U};terms[ix[v]]+=1
            for u,w in edges:
                if u in S and w in S:terms[iy[u,w]]=1
            terms=sorted((i,c) for i,c in terms.items() if c)
            violation=sum(c*values[i] for i,c in terms);maximum=max(maximum,violation)
            key=(v,tuple(U))
            if violation>1e-7 and key not in known:
                candidates.append((key,{'vertex':v,'subset':U,'violation_at_discovery':violation,'iteration':iteration},terms))
        entry={'iteration':iteration,'objective':obj.Value(),'new_violated_subsets':len(candidates),'maximum_detected_violation':maximum,'rows':len(rows)}
        steps.append(entry);print(json.dumps({'root':root,**entry}),flush=True)
        if not candidates or iteration==60:break
        for key,witness,terms in candidates:
            known.add(key);row={'name':'forest_'+str(len(added)),'terms':terms,'sense':'le','rhs':0}
            witness['row_index']=len(rows);added.append(witness);rows.append(row);install(row)
    model['base_model_sha256']=sha(base);model['source_sha256_220']=sha(__file__)
    model['subset_witnesses']=added;model['scope']+=' Round220 adds necessary induced-forest subset rows. Floating separation does not prove closure.'
    save(F/'model.json',model)
    D=10**6;duals=[c.dual_value() for c in constraints]
    weights=[max(0,round(v*D)) if row['sense']=='le' else round(v*D) for row,v in zip(rows,duals)]
    residual=[D*c for c in model['objective']];rhs=0
    for row,w in zip(rows,weights):
        rhs+=row['rhs']*w
        for i,a in row['terms']:residual[i]-=a*w
    upper=rhs+sum(max(r,0) for r in residual);bound=Q(upper,D)
    save(F/'upper-certificate.json',{'scale':D,'weights':weights,'residual':residual,'positive_residual':[max(r,0) for r in residual],
        'upper_numerator':upper,'upper_bound':rat(bound),'model_sha256':sha(F/'model.json')})
    report={'root':root,'status':'OPTIMAL_NATIVE','objective':obj.Value(),'exact_upper':rat(bound),'seconds':time.monotonic()-started,
        'added_subset_count':len(added),'steps':steps,'values':values,'duals':duals,'model_sha256':sha(F/'model.json'),
        'solver_version':solver.SolverVersion(),'no_new_violations_at_tolerance':not bool(candidates)}
    save(F/'native-result.json',report);summary.append({k:v for k,v in report.items() if k not in ['values','duals','steps']})
    save(H/'data/forest-summary.json',summary)
