"""Independent exhaustive reconstruction from rule predicates and encoded counts."""
from pathlib import Path
from fractions import Fraction
import collections,gzip,hashlib,json,sys,time
HERE=Path(__file__).resolve().parents[1];ROOT=HERE.parents[1]
sys.path.insert(0,str(ROOT/'work/solver_packages'))
import numpy as np
read=lambda p:json.loads(p.read_text(encoding='utf-8-sig'));sha=lambda b:hashlib.sha256(b).hexdigest();tag='enriched-' if '--enriched' in sys.argv else '';start=time.monotonic()
md=read(HERE/f'data/{tag}model.json');result=read(HERE/f'data/{tag}analysis.json');sm=read(ROOT/'milestones/59-extended-share-window/extended/data/model.json');geo=read(ROOT/'milestones/59-extended-share-window/data/geometry.json')['patterns']
with np.load(HERE/f'build/{tag}graph.npz') as z:a={k:z[k] for k in z.files}
for k,h in md['arrays_sha256'].items():assert sha(a[k].tobytes())==h
prior=read(ROOT/'milestones/67-critical-family-charge/data/full-model.json')
for k in ['patterns','prefixes','compatible_shapes','states']:assert md[k]==prior[k]
def canon(w):
 names={};return tuple(names.setdefault(x,len(names)) for x in w)
def codeof(cs):
 k=0
 for c in cs:k=6*k+c-1
 return k
reference=read(ROOT/'milestones/54-share-coverage/data/keys_235.json')['keys'];rows=[(w,[x[0] for x in bs]) for w,bs in reference]+read(ROOT/'milestones/39-audited-bound-236/data/exclusion-catalogue.json')
lookup=collections.defaultdict(set)
for ds,cs in rows:
 lookup[canon(ds)].add(codeof(cs));lookup[canon(ds[::-1])].add(codeof(cs[::-1]))
C=np.array([[i//6**k%6+1 for k in range(5,-1,-1)] for i in range(6**6)],dtype=np.int16);codes=np.arange(len(C));B=6**5;N=sm['states'];shape={tuple(w):i for i,w in enumerate(sm['direction_shapes'])}
# Enumerate actual contiguous groups once; uniqueness and coverage are checked.
group=a['direction'].astype(np.int64)*len(md['prefixes'])+a['history'];cuts=np.r_[0,np.flatnonzero(group[1:]!=group[:-1])+1,len(group)];groups={}
for l,r in zip(cuts[:-1],cuts[1:]):
 key=int(group[l]);assert key not in groups;groups[key]=(int(l),int(r))
visited=set();checked=0
for q,prefix in enumerate(md['prefixes']):
 for di,ds in enumerate(sm['extensions']):
  ps,ts=shape[canon(ds[:8])],shape[canon(ds[1:])]
  if q and md['compatible_shapes'][q]!=ps:continue
  valid=np.ones(len(C),dtype=bool)
  for offset in range(5):
   for width in range(2,7-offset):
    sub=canon(ds[2+offset:3+offset+width]);value=(codes//6**(6-offset-width))%6**width
    if sub in lookup:valid&=~np.isin(value,list(lookup[sub]))
  for rule in md.get('additional_proved_rules',[]):
   size=len(rule['dirs']);positions=rule.get('positions',[rule.get('position')])
   for r in range(10-size):
    w=ds[r:r+size]
    for rev in [False,True]:
     if canon(w[::-1] if rev else w)!=tuple(rule['dirs']):continue
     ix=[r+size-i if rev else r+i for i in positions]
     if min(ix)<3 or max(ix)>8:continue
     values=C[:,np.array(ix)-3]
     if rule['source'].startswith('47'):bad=values[:,0]<=1
     elif rule['kind']=='sum':bad=(values.sum(axis=1)<=rule['cap'])&(values.max(axis=1)<6)
     else:bad=np.all(values<=np.array(rule['caps']),axis=1)
     valid&=~bad
  credit=np.full(len(C),geo[di]['share_lower'],dtype=np.int16)
  for w,counts,L in md['forward_rules']:
   for reverse in [False,True]:
    word=canon(w[::-1] if reverse else w);counts2=counts[::-1] if reverse else counts
    if canon(ds[-6:])==word:
     hit=np.all(C[:,1:]==counts2,axis=1);credit[hit]=np.maximum(credit[hit],L)
  hist=tuple(prefix)+(di,);nq=0
  for j,p in enumerate(md['prefixes']):
   if p and len(p)<=len(hist) and hist[-len(p):]==tuple(p) and len(p)>len(md['prefixes'][nq]):nq=j
  for rule in md['patterns']:
   if len(hist)<3 or hist[-3:]!=tuple(rule['signature']):continue
   hit=np.ones(len(C),dtype=bool)
   for k,cap in rule['caps'].items():hit&=C[:,int(k)]<=cap
   if rule['mode']=='exclusion':valid&=~hit
   else:credit=np.maximum(credit,rule['geometric_lower']);credit[hit]=np.maximum(credit[hit],rule['lower'])
  key=di*len(md['prefixes'])+q;want=codes[valid]
  if len(want)==0:assert key not in groups;continue
  l,r=groups[key];visited.add(key);assert np.array_equal(a['count_code'][l:r],want)
  assert np.array_equal(a['U'][l:r],(ps*B if q==0 else N+(q-1)*B)+want//6)
  assert np.array_equal(a['V'][l:r],(ts*B if nq==0 else N+(nq-1)*B)+want%B)
  assert np.array_equal(a['weight'][l:r],120*C[valid,-1].astype(np.int64)+credit[valid]);checked+=r-l
assert visited==set(groups) and checked==md['edges']
raw=gzip.decompress((HERE/f'data/{tag}potential.i64.gz').read_bytes());assert sha(raw)==result['potential_sha256'];pi=np.frombuffer(raw,dtype='<i8');mu=Fraction(result['integer_mean']);p,d=mu.numerator,mu.denominator
assert len(pi)==md['states'] and min(pi)==0 and max(pi)==result['potential_range']
assert np.all(p+pi[a['V']]<=d*a['weight'].astype(np.int64)+pi[a['U']])
cycle=[e['edge'] for e in result['cycle']];assert all(a['V'][e]==a['U'][cycle[(i+1)%len(cycle)]] for i,e in enumerate(cycle));assert d*sum(int(a['weight'][e]) for e in cycle)==p*len(cycle)
assert Fraction(result['conditional_bound'])==Fraction(1098960*d+8*p+int(max(pi)),p+4200*d)
out=dict(status='PASS',model=tag or 'baseline',edges=checked,groups=len(groups),exact_mean=str(mu),potential_range=int(max(pi)),attaining_cycle_edges=len(cycle),seconds=time.monotonic()-start,scope='Independent complete transition, weight and exact-potential reconstruction. Rule proofs are inherited. Does not supply full arbitrary-snake normalization/history assembly or complete Lean graph replay.')
(HERE/f'data/{tag}verification.json').write_text(json.dumps(out,indent=2)+'\n');print(out,flush=True)
