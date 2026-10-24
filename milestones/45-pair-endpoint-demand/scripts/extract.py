"""Extract the endpoint-avoidance core and identify the endpoint demand set."""
from probe import HERE,ROOT,DS,W,TaggedEncoding
import importlib.util,itertools,json
spec=importlib.util.spec_from_file_location('ordinary',ROOT/'milestones/38-four-position-obstruction/scripts/certify.py')
old=importlib.util.module_from_spec(spec);spec.loader.exec_module(old);old.HERE=HERE
for d in ['certificates','logs','lean','build']:(HERE/d).mkdir(exist_ok=True)
e=TaggedEncoding(W,[(0,21)]*7,radius=4)
lits=[-e.var[W[j]^(1<<a)^(1<<b)] for j in [2,6] for a,b in itertools.combinations(range(9),2) if a not in (DS[j-1],DS[j]) and b not in (DS[j-1],DS[j])]
e.atmost(lits,7,('ends',))
avoid={v for v in range(512) if (v^W[2]).bit_count()<=2}
endvars={v:k for k,(kind,v,*_) in e.meaning.items() if kind=='e'}
for v in sorted(avoid):e.add([-endvars[v]],('avoid',v))
prefix=HERE/'certificates/endpoint451'
old.writecnf(prefix.with_suffix('.full.cnf'),e.nv,e.clauses)
old.run([old.LEANBIN/'cadical.exe','-q','--no-binary',prefix.with_suffix('.full.cnf'),prefix.with_suffix('.drat')],'endpoint451-cadical.txt',20)
report=old.run([ROOT/'work/share-wheels/drat-trim.exe',prefix.with_suffix('.full.cnf'),prefix.with_suffix('.drat'),'-c',prefix.with_suffix('.core.cnf')],'endpoint451-drat-check.txt');assert 's VERIFIED' in report
raw=old.readcnf(prefix.with_suffix('.core.cnf'));lookup={tuple(sorted(c)):j for j,c in enumerate(e.clauses)}
ids=[lookup[tuple(sorted(c))] for c in raw]
demand=sorted(e.tags[j][1] for j in ids if e.tags[j][0]=='avoid')
out=dict(directions=DS,positions=[2,6],joint_cap=7,avoid_vertices=sorted(avoid),endpoint_demand=demand,ordinary_clause_ids=[j+1 for j in ids if e.tags[j][0]!='avoid'],endpoint_clause_ids=[j+1 for j in ids if e.tags[j][0]=='avoid'],clauses=len(ids))
(HERE/'data/core.json').write_text(json.dumps(out,indent=2)+'\n')
print('Core clauses',len(ids),'endpoint demand',demand,'offset bits',[[i for i in range(9) if (v^W[2])>>i&1] for v in demand],flush=True)
