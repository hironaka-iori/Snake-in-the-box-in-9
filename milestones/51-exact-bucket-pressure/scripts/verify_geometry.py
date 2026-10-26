"""Independently check saved forests, share values and every finite-model potential."""
from pathlib import Path
from fractions import Fraction
import collections,gzip,hashlib,itertools,json,sys
HERE=Path(__file__).resolve().parents[1];ROOT=HERE.parents[1]
sys.path.insert(0,str(ROOT/'work/solver_packages'));import numpy as np
pairs=list(itertools.combinations(range(9),2))
def sha(b):return hashlib.sha256(b).hexdigest()
def nb(v):return {v^(1<<d) for d in range(9)}
def alpha(S,v):return sum(not({v^(1<<a),v^(1<<b),v^(1<<a)^(1<<b)}&S) for a,b in pairs)
def shares(S,centres):
 out=[]
 for c in centres:
  total=0
  for q in nb(c):
   degree=len(nb(q)&S)
   empty=sum(not({q,q^(1<<a),q^(1<<b),q^(1<<a)^(1<<b)}&S) for a,b in pairs)
   total+=12*empty//degree if degree else 0
  out.append(total)
 return out
def forest(S,W):
 B={v for v in range(512) if min((v^c).bit_count() for c in W[1:-1])<=4}
 assert set(W)<=S<=B
 degree={v:len(nb(v)&S) for v in S};assert all(d<=2 for d in degree.values())
 inside=[v for v in S if nb(v)<=B];assert all(degree[v]>0 for v in inside)
 assert sum(degree[v]==1 for v in inside)<=2
 todo=set(S)
 while todo:
  seed=todo.pop();component={seed};queue=[seed]
  while queue:
   v=queue.pop()
   for w in nb(v)&todo:todo.remove(w);component.add(w);queue.append(w)
  assert sum(degree[v] for v in component)==2*(len(component)-1)
 return [alpha(S,v) for v in W[1:-1]]
positive=[];files=list(HERE.glob('pass*/data/queries/*.json'))+list((HERE/'data/share-screen').glob('*.json'))
for file in files:
 r=json.loads(file.read_text())
 if r['status'] not in ['SAT','FEASIBLE']:continue
 ds=r.get('directions',r.get('dirs'));W=[0]
 for d in ds:W.append(W[-1]^(1<<d))
 S=set(r['selected']);counts=forest(S,W);bounds=r.get('bounds',r.get('alpha'))
 assert counts==r['census']['alpha'] and all(lo<=a<=hi for a,(lo,hi) in zip(counts,bounds))
 if r.get('joint_cap') is not None:assert sum(counts[j-1] for j in r['positions'])<=r['joint_cap']
 ss=shares(S,W[1:-1]);assert ss==r['census']['share'] and sum(ss)==r['census']['total_share']
 if 'cap' in r:assert sum(ss)<=r['cap']
 positive.append(dict(file=file.relative_to(HERE).as_posix(),sha256=sha(file.read_bytes()),counts=counts,total_share=sum(ss)))
def canon(ds):
 names={};return tuple(names.setdefault(d,len(names)) for d in ds)
def code(cs):
 v=0
 for c in cs:v=6*v+c-1
 return v
models=[]
for name in [f'pass{k}' for k in range(1,6)]+['share-model']:
 folder=HERE/name;meta=json.loads((folder/'data/model.json').read_text());r=json.loads((folder/'data/analysis.json').read_text())
 with np.load(folder/'build/graph.npz') as z:a={k:z[k] for k in z.files}
 for k,digest in meta['arrays_sha256'].items():assert sha(a[k].tobytes())==digest
 keep=~a['excluded'];U=a['U'][keep];V=a['V'][keep]
 scale=336 if name=='share-model' else 168
 weights=scale*a['count'][keep].astype(np.int64)+(scale//7)*a['demand'][keep]+42*a['share'][keep]
 if name=='share-model':weights+=a['share_lower'][keep]
 mean=Fraction(r['integer_weight_mean']);p,q=mean.numerator,mean.denominator
 encoded=gzip.decompress((folder/'data/potential.i64.gz').read_bytes());potential=np.frombuffer(encoded,dtype='<i8')
 assert sha(encoded)==r['potential_sha256'] and np.all(p+potential[V]<=q*weights+potential[U])
 shapes={tuple(s):i for i,s in enumerate(meta['direction_shapes'])};cycle=r['cycle']
 for j,row in enumerate(cycle):
  ds,cs=row['directions'],row['counts'];u=shapes[canon(ds[:7])]*6**6+code(cs[:6]);v=shapes[canon(ds[1:])]*6**6+code(cs[1:])
  assert u==row['state'] and v==row['next_state']==cycle[(j+1)%len(cycle)]['state']
  matches=np.flatnonzero(keep&(a['U']==u)&(a['V']==v)&(a['count_code']==code(cs)))
  assert any(meta['extensions'][int(a['direction'][i])]==ds and int(a['demand'][i])==row['demand'] and int(a['share'][i])==row['share_event'] and (name!='share-model' or int(a['share_lower'][i])==row['share_lower']) for i in matches)
  assert row['weight']==scale*cs[-1]+(scale//7)*row['demand']+42*row['share_event']+row.get('share_lower',0)
 assert Fraction(sum(row['weight'] for row in cycle),len(cycle))==mean
 assert mean/scale==Fraction(r['normalized_charge_mean'])
 models.append(dict(model=name,edges=len(U),normalized_mean=str(mean/scale),potential_range=r['potential_range'],denominator=q))
summary=dict(status='PASS',positive_controls=len(positive),controls=positive,models=models,scope='Exact finite checks of saved local forests and model potentials. Numerical exclusions remain unproved until their separate certificates and geometry are checked; no new global bound.')
(HERE/'data/geometry-verification.json').write_text(json.dumps(summary,indent=2)+'\n')
print('Positive controls',len(positive),'models',models,flush=True)
