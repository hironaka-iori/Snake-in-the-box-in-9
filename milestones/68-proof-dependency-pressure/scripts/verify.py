"""Independent weights and exact certificate check after deleting numerical shares."""
from pathlib import Path
from fractions import Fraction
import gzip,hashlib,json,sys,time
HERE=Path(__file__).resolve().parents[1];ROOT=HERE.parents[1]
sys.path.insert(0,str(ROOT/'work/solver_packages'))
import numpy as np
read=lambda p:json.loads(p.read_text(encoding='utf-8-sig'));sha=lambda b:hashlib.sha256(b).hexdigest();start=time.monotonic()
PREV=ROOT/'milestones/67-critical-family-charge';SOURCE=ROOT/'milestones/59-extended-share-window/extended'
meta=read(HERE/'data/share-clean-model.json');oldmeta=read(PREV/'data/full-model.json');sm=read(SOURCE/'data/model.json')
with np.load(HERE/'build/share-clean-graph.npz') as z:a={k:z[k] for k in z.files}
with np.load(PREV/'build/full-graph.npz') as z:old={k:z[k] for k in z.files}
with np.load(SOURCE/'build/graph.npz') as z:s={k:z[k] for k in z.files}
for data,md in [(a,meta),(old,oldmeta),(s,sm)]:
 for k,h in md['arrays_sha256'].items():assert sha(data[k].tobytes())==h
for k in ['U','V','source_edge','history']:assert np.array_equal(a[k],old[k])
assert meta['patterns']==oldmeta['patterns'] and meta['prefixes']==oldmeta['prefixes']
def canon(w):
 labels=list(dict.fromkeys(w));return tuple(labels.index(x) for x in w)
rules=read(ROOT/'milestones/57-replacement-share-family/combined/data/model.json')['share_rules']
allowed=[r for r in rules if r.get('status')!='NUMERICAL_ONLY'];assert len(allowed)==8
assert all(r['milestone'] in [51,52,53] for r in allowed)
# Validate forward proof receipts and the reversal theorem receipt separately.
receipts=[]
for milestone in ['51-exact-bucket-pressure','52-share-on-235','53-shares-on-sat-obstruction','54-share-coverage']:
 p=ROOT/f'milestones/{milestone}/data/verification.json';r=read(p);assert r['status']=='PASS'
 receipts.append(dict(path=str(p.relative_to(ROOT)),sha256=sha(p.read_bytes()),recorded_status=r.get('status')))
geo=read(ROOT/'milestones/59-extended-share-window/data/geometry.json')['patterns']
# Each suffix/count signature has its own applicable checked credit.
lookup={}
for di,ds in enumerate(sm['extensions']):
 lookup[di]=[r for r in allowed if canon(ds[-6:])==tuple(r['directions'])]
changed=violations=0
for q,prefix in enumerate(meta['prefixes']):
 ix=np.flatnonzero(a['history']==q);src=a['source_edge'][ix];direction=s['direction'][src];codes=s['count_code'][src]
 lower=np.array([g['share_lower'] for g in geo],dtype=np.int16)[direction]
 for di in np.unique(direction):
  pos=np.flatnonzero(direction==di)
  for rule in lookup[int(di)]:
   key=sum((c-1)*6**(4-j) for j,c in enumerate(rule['counts']))
   hit=pos[codes[pos]%(6**5)==key];lower[hit]=np.maximum(lower[hit],rule['lower'])
 for pat in meta['patterns']:
  if pat['mode']=='exclusion':continue
  sig=tuple(pat['signature'])
  if tuple(prefix)!=sig[:2]:continue
  eligible=direction==sig[2]
  lower[eligible]=np.maximum(lower[eligible],pat['geometric_lower'])
  for k,cap in pat['caps'].items():eligible&=(codes//6**(5-int(k)))%6+1<=cap
  lower[eligible]=np.maximum(lower[eligible],pat['lower'])
 expected=120*s['count'][src].astype(np.int64)+lower
 assert np.array_equal(a['weight'][ix],expected)
 changed+=int(np.count_nonzero(expected!=old['weight'][ix]))
result=read(HERE/'data/share-clean-analysis.json');raw=gzip.decompress((HERE/'data/share-clean-potential.i64.gz').read_bytes())
assert sha(raw)==result['potential_sha256'];pi=np.frombuffer(raw,dtype='<i8')
assert len(pi)==meta['states'] and min(pi)==0 and max(pi)==result['potential_range']
mu=Fraction(result['integer_mean']);p,d=mu.numerator,mu.denominator
assert np.all(p+pi[a['V']]<=d*a['weight'].astype(np.int64)+pi[a['U']])
ci=[r['edge'] for r in result['cycle']]
assert all(a['V'][e]==a['U'][ci[(i+1)%len(ci)]] for i,e in enumerate(ci))
assert d*sum(int(a['weight'][e]) for e in ci)==p*len(ci)
bound=Fraction(1098960*d+8*p+int(max(pi)),p+4200*d)
assert bound==Fraction(result['conditional_bound']) and bound<235
assert changed==read(HERE/'data/share-ablation.json')['full_edges_losing_credit']
out=dict(status='PASS',states=len(pi),edges=len(a['U']),changed_edges=changed,checked_oriented_share_rules=8,removed_numerical_oriented_share_rules=24,exact_mean=str(mu),potential_range=int(max(pi)),attaining_cycle_edges=len(ci),conditional_bound=str(bound),conditional_integer_bound=234,prior_proof_receipts=receipts,seconds=time.monotonic()-start,scope='Independent weight reconstruction and all-edge potential verification. Graph topology is inherited unchanged from verified milestone 67. Older share proof receipts are pinned, not rebuilt. Numerical count exclusions and arbitrary-snake assembly remain pending.')
(HERE/'data/verification.json').write_text(json.dumps(out,indent=2)+'\n');print(out,flush=True)
