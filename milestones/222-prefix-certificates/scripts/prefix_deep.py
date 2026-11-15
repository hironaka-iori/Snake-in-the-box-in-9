"""Bounded induced-prefix branching with exact weighted upper certificates."""
from pathlib import Path
from fractions import Fraction as Q
import hashlib,json,sys,time
H=Path(__file__).resolve().parents[1];R=H.parents[1];P=R/'milestones/221-square-parity'
sys.path.insert(0,str(R/'work/solver_packages'))
from ortools.linear_solver import pywraplp

def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def save(p,x):p.write_text(json.dumps(x,indent=2)+'\n',encoding='utf-8')
def key(path):return '-'.join(map(str,path))
models={t:json.loads((P/'data'/f'long-{t}/model.json').read_bytes()) for t in [0,78]}
neighbours={t:{u:sorted(v for v in m['vertices'] if (u^v).bit_count()==1) for u in m['vertices']} for t,m in models.items()}
first=json.loads((P/'data/first-summary.json').read_bytes())
assert len(first)==14 and sha(P/'data/first-audit.json')=='84283463d10dc79cc5e375ac1968c562b3e38c47a1a29f5ced842c4ac52b8562'
folder=H/'data/deep-cases';assert not folder.exists();folder.mkdir()
assert sha(H/'data/continuation-ledger.json')=='323d5c00de98df6bdfdcd03e23ba1692acf98c15ee6e8d45aa125804ac9f3253'
ledger=json.loads((H/'data/continuation-ledger.json').read_bytes())
ledger['maximum_prefix_edges']=8
assert not ledger['queue']

def candidates(path):
 return [v for v in neighbours[path[0]][path[-1]] if v not in path and all((v^u).bit_count()!=1 for u in path[:-1])]

def solve(path):
 root=path[0];m=models[root];names={n:i for i,n in enumerate(m['variables'])}
 added=[{'name':f'prefix_x_{v}','terms':[[names[f'x{v}'],1]],'sense':'eq','rhs':1} for v in path[1:]]
 added += [{'name':f'prefix_nonendpoint_{v}','terms':[[names[f'e{v}'],1]],'sense':'eq','rhs':0} for v in path[1:] if f'e{v}' in names]
 rows=m['rows']+added;solver=pywraplp.Solver.CreateSolver('GLOP');solver.SetNumThreads(1);solver.SetTimeLimit(45000)
 z=[solver.NumVar(0,1,n) for n in m['variables']];constraints=[]
 for row in rows:
  c=solver.Constraint(row['rhs'] if row['sense']=='eq' else -solver.infinity(),row['rhs'],row['name'])
  for i,a in row['terms']:c.SetCoefficient(z[i],a)
  constraints.append(c)
 obj=solver.Objective()
 for i,a in enumerate(m['objective']):obj.SetCoefficient(z[i],a)
 obj.SetMaximization();start=time.monotonic();status=solver.Solve()
 report={'root':root,'prefix':path,'base_model_sha256':sha(P/'data'/f'long-{root}/model.json'),'source_sha256':sha(__file__),'appended_rows':added,'row_count':len(rows),'native_status_code':status,'solver_version':solver.SolverVersion(),'seconds':time.monotonic()-start}
 if status!=solver.OPTIMAL:report['status']='PENDING_NATIVE_WITHOUT_EXACT_CERTIFICATE';return report
 D=10**6;weights=[max(0,round(c.dual_value()*D)) if row['sense']=='le' else round(c.dual_value()*D) for row,c in zip(rows,constraints)]
 residual=[D*c for c in m['objective']];rhs=0
 for row,w in zip(rows,weights):
  rhs+=row['rhs']*w
  for i,a in row['terms']:residual[i]-=a*w
 upper=rhs+sum(max(r,0) for r in residual);bound=Q(upper,D)
 report.update(status='EXACT_UPPER_CERTIFICATE',objective=obj.Value(),scale=D,nonzero_weights=[[i,w] for i,w in enumerate(weights) if w],residual=residual,upper_numerator=upper,upper_bound=[bound.numerator,bound.denominator])
 return report

pending=[(k,n) for k,n in ledger['nodes'].items() if n['status']=='PENDING_DEPTH_LIMIT']
assert len(pending)==1
for k,n in pending:
 children=candidates(n['prefix']);assert children
 n.update(status='EXPANDED',next_vertices=children,children=[key(n['prefix']+[v]) for v in children])
 for v,c in zip(children,n['children']):
  assert c not in ledger['nodes'];ledger['nodes'][c]={'prefix':n['prefix']+[v],'parent':k,'status':'PENDING'};ledger['queue'].append(c)
start=time.monotonic()
while ledger['queue'] and ledger['jobs']<ledger['maximum_jobs'] and time.monotonic()-start<180:
 k=ledger['queue'].pop(0);node=ledger['nodes'][k];path=node['prefix'];children=candidates(path)
 assert len(path)==len(set(path)) and all((u^v).bit_count()==1 for u,v in zip(path,path[1:]))
 assert all((path[i]^path[j]).bit_count()!=1 for i in range(len(path)) for j in range(i+2,len(path)))
 if not children:
  node['status']='EXCLUDED_NO_NEXT_VERTEX';node['next_vertices']=[]
 else:
  report=solve(path);ledger['jobs']+=1;out=folder/(k+'.json');save(out,report)
  node.update(certificate=str(out.relative_to(R)),sha256=sha(out))
  if report['status']!='EXACT_UPPER_CERTIFICATE':node['status']='PENDING_NATIVE_WITHOUT_EXACT_CERTIFICATE'
  else:
   node['upper_bound']=report['upper_bound']
   if Q(*report['upper_bound'])<94:node['status']='EXCLUDED_BOUND'
   elif len(path)-1==ledger['maximum_prefix_edges']:node['status']='PENDING_DEPTH_LIMIT'
   else:
    node['status']='EXPANDED';node['next_vertices']=children;node['children']=[key(path+[v]) for v in children]
    for v,c in zip(children,node['children']):
     assert c not in ledger['nodes'];ledger['nodes'][c]={'prefix':path+[v],'parent':k,'status':'PENDING'};ledger['queue'].append(c)
 save(H/'data/deep-ledger.json',ledger)
 print(json.dumps({'prefix':path,'status':node['status'],'upper_bound':node.get('upper_bound'),'jobs':ledger['jobs'],'queue':len(ledger['queue'])}),flush=True)
ledger['stop_reason']='QUEUE_FINISHED' if not ledger['queue'] else 'JOB_LIMIT' if ledger['jobs']>=ledger['maximum_jobs'] else 'BATCH_WALL_LIMIT'
ledger['seconds']=time.monotonic()-start
save(H/'data/deep-ledger.json',ledger)
counts={s:sum(n['status']==s for n in ledger['nodes'].values()) for s in sorted({n['status'] for n in ledger['nodes'].values()})}
summary={'jobs':ledger['jobs'],'nodes':len(ledger['nodes']),'counts':counts,'stop_reason':ledger['stop_reason'],'seconds':ledger['seconds'],'ledger_sha256':sha(H/'data/deep-ledger.json'),'by_depth':{str(d):{s:sum(n['status']==s and len(n['prefix'])-1==d for n in ledger['nodes'].values()) for s in counts} for d in range(1,9)}}
save(H/'data/deep-summary.json',summary);print(json.dumps(summary),flush=True)
