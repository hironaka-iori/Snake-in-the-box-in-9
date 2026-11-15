"""Exact upper certificates for the seven possible first-step branches."""
from pathlib import Path
from fractions import Fraction as Q
import hashlib,json,sys,time
H=Path(__file__).resolve().parents[1];R=H.parents[1]
sys.path.insert(0,str(R/'work/solver_packages'))
from ortools.linear_solver import pywraplp
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def save(p,x):p.write_text(json.dumps(x,indent=2)+'\n',encoding='utf-8')
summary=[]
for root in [0,78]:
    base=H/'data'/f'long-{root}'/'model.json';m=json.loads(base.read_bytes());names={n:i for i,n in enumerate(m['variables'])}
    first=sorted(v if u==root else u for u,v in m['edges'] if root in [u,v]);assert len(first)==7
    folder=H/'data'/f'first-{root}';assert not folder.exists();folder.mkdir()
    for v in first:
        branch={'name':'fixed_first_vertex','terms':[[names[f'x{v}'],1]],'sense':'eq','rhs':1}
        rows=m['rows']+[branch];solver=pywraplp.Solver.CreateSolver('GLOP');solver.SetNumThreads(1);solver.SetTimeLimit(45000)
        z=[solver.NumVar(0,1,n) for n in m['variables']];constraints=[]
        for row in rows:
            c=solver.Constraint(row['rhs'] if row['sense']=='eq' else -solver.infinity(),row['rhs'],row['name'])
            for i,a in row['terms']:c.SetCoefficient(z[i],a)
            constraints.append(c)
        obj=solver.Objective()
        for i,a in enumerate(m['objective']):obj.SetCoefficient(z[i],a)
        obj.SetMaximization();started=time.monotonic();status=solver.Solve();seconds=time.monotonic()-started
        assert status==solver.OPTIMAL
        D=10**6;weights=[max(0,round(c.dual_value()*D)) if row['sense']=='le' else round(c.dual_value()*D) for row,c in zip(rows,constraints)]
        residual=[D*c for c in m['objective']];rhs=0
        for row,w in zip(rows,weights):
            rhs+=row['rhs']*w
            for i,a in row['terms']:residual[i]-=a*w
        upper=rhs+sum(max(r,0) for r in residual);bound=Q(upper,D)
        out=folder/f'vertex-{v}.json'
        report={'root':root,'first_vertex':v,'base_model_sha256':sha(base),'source_sha256':sha(__file__),'appended_row':branch,
            'status':'OPTIMAL_NATIVE','seconds':seconds,'objective':obj.Value(),'solver_version':solver.SolverVersion(),
            'scale':D,'nonzero_weights':[[i,w] for i,w in enumerate(weights) if w],'row_count':len(rows),
            'residual':residual,'upper_numerator':upper,'upper_bound':[bound.numerator,bound.denominator],
            'values':[x.solution_value() for x in z],'scope':'Conditional fixed-first-neighbour LP bound. The seven cases cover every actual partner; rational mixtures need not choose one.'}
        save(out,report);row={'root':root,'first_vertex':v,'objective':obj.Value(),'upper_bound':report['upper_bound'],'upper_float':float(bound),'seconds':seconds,'sha256':sha(out)}
        summary.append(row);save(H/'data/first-summary.json',summary);print(json.dumps(row),flush=True)
