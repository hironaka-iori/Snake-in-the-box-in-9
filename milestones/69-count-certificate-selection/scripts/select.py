"""Restore count transitions and select the exclusions needed by a fixed potential.
All count positions are checked for the pinned reference catalogue. Additional
keys use the exact contiguous-subwindow basis from milestone 68.
"""
from pathlib import Path
import collections,gzip,hashlib,itertools,json,sys,time
HERE=Path(__file__).resolve().parents[1];ROOT=HERE.parents[1]
sys.path.insert(0,str(ROOT/'work/solver_packages'))
import numpy as np
read=lambda p:json.loads(p.read_text(encoding='utf-8-sig'));sha=lambda b:hashlib.sha256(b).hexdigest();start=time.monotonic();numerator=int(sys.argv[1]) if len(sys.argv)>1 else 14392;suffix='' if numerator==14392 else '-'+str(numerator)
P=ROOT/'milestones/68-proof-dependency-pressure';md=read(P/'data/share-clean-model.json');res=read(P/'data/share-clean-analysis.json')
sm=read(ROOT/'milestones/59-extended-share-window/extended/data/model.json');geo=read(ROOT/'milestones/59-extended-share-window/data/geometry.json')['patterns']
raw=gzip.decompress((P/'data/share-clean-potential.i64.gz').read_bytes());assert sha(raw)==res['potential_sha256'];pi=np.frombuffer(raw,dtype='<i8')
sub=json.loads(gzip.decompress((P/'data/count-subsumption.json.gz').read_bytes()));additional=sub['needed'];ref=read(ROOT/'milestones/54-share-coverage/data/keys_235.json')['keys']
rules=read(ROOT/'milestones/57-replacement-share-family/combined/data/model.json')['share_rules'];rules=[r for r in rules if r.get('status')!='NUMERICAL_ONLY']
def canon(w):
 labels=list(dict.fromkeys(w));return tuple(labels.index(x) for x in w)
def encode(cs):
 code=0
 for c in cs:code=6*code+c-1
 return code
def tables(rows):
 out={}
 for i,(ds,cs) in enumerate(rows):
  for w,c in [(ds,cs),(ds[::-1],cs[::-1])]:
   key=canon(w)
   if key not in out:out[key]=np.full(6**len(cs),-1,dtype=np.int32)
   index=encode(c);assert out[key][index] in (-1,i);out[key][index]=i
 return out
reference_rows=[(w,[lo for lo,hi in bs]) for w,bs in ref]
reference_rows += read(ROOT/'milestones/39-audited-bound-236/data/exclusion-catalogue.json')
def canonical_key(w,c):return min((canon(w),tuple(c)),(canon(w[::-1]),tuple(c[::-1])))
reference_rows=sorted({canonical_key(w,c) for w,c in reference_rows})
base=tables(reference_rows);extra=tables(additional)
C=np.array(list(itertools.product(range(1,7),repeat=6)),dtype=np.int16);codes=np.arange(6**6,dtype=np.int32);B=6**5;N=sm['states'];sid={tuple(w):i for i,w in enumerate(sm['direction_shapes'])}
prefixes=[tuple(p) for p in md['prefixes']];clauses=collections.Counter();examples={};totals=collections.Counter();rowstats=[]
for di,ds in enumerate(sm['extensions']):
 ps=sid[canon(ds[:8])];ts=sid[canon(ds[1:])];banned=np.zeros(len(C),dtype=bool);matches=[]
 for width in range(2,7):
  for offset in range(7-width):
   word=canon(ds[2+offset:3+offset+width]);subcode=(codes//6**(6-offset-width))%6**width
   if word in base:banned|=base[word][subcode]>=0
   if word in extra:matches.append(extra[word][subcode])
 keep=np.flatnonzero(~banned);cs=C[keep];code=codes[keep];matched=np.stack(matches,axis=1)[keep] if matches else np.empty((len(keep),0),dtype=np.int32)
 credit=np.full(len(keep),geo[di]['share_lower'],dtype=np.int16)
 for rule in rules:
  if canon(ds[-6:])==tuple(rule['directions']):
   hit=np.all(cs[:,-5:]==rule['counts'],axis=1);credit[hit]=np.maximum(credit[hit],rule['lower'])
 qs=[0]+[q for q in range(1,len(prefixes)) if md['compatible_shapes'][q]==ps]
 for q in qs:
  history=prefixes[q]+(di,);possible=[(len(t),j) for j,t in enumerate(prefixes) if t and len(t)<=len(history) and history[-len(t):]==t];nq=max(possible)[1] if possible else 0
  if nq:assert md['compatible_shapes'][nq]==ts
  U=ps*B+code//6 if q==0 else N+(q-1)*B+code//6
  V=ts*B+code%B if nq==0 else N+(nq-1)*B+code%B
  lower=credit.copy();reject=np.zeros(len(code),dtype=bool)
  for pat in md['patterns']:
   if len(history)<3 or history[-3:]!=tuple(pat['signature']):continue
   qualifies=np.ones(len(code),dtype=bool)
   for k,cap in pat['caps'].items():qualifies&=cs[:,int(k)]<=cap
   if pat['mode']=='exclusion':reject|=qualifies
   else:
    lower=np.maximum(lower,pat['geometric_lower']);lower[qualifies]=np.maximum(lower[qualifies],pat['lower'])
  weight=120*cs[:,-1].astype(np.int64)+lower
  slack=29*weight+pi[U]-pi[V]-numerator
  bad=np.flatnonzero((slack<0)&~reject)
  totals['candidate_edges']+=int((~reject).sum());totals['violating_edges']+=len(bad)
  for j in bad:
   clause=tuple(sorted(set(int(k) for k in matched[j] if k>=0)))
   if not clause:raise AssertionError(('uncovered negative edge',di,q,int(code[j]),int(slack[j])))
   clauses[clause]+=1
   if clause not in examples:examples[clause]=dict(direction=di,history=q,count_code=int(code[j]),slack=int(slack[j]))
 rowstats.append(dict(direction=di,base_excluded=int(banned.sum()),contexts=len(qs)))
 if di%60==0:print('Scanned',di,'of',len(sm['extensions']),'negative edges',totals['violating_edges'],'clauses',len(clauses),flush=True)
forced={c[0] for c in clauses if len(c)==1};remaining=[c for c in clauses if not forced.intersection(c)]
selected=set(forced)
while remaining:
 score=collections.Counter(k for c in remaining for k in c);chosen=min(score,key=lambda k:(-score[k],k));selected.add(chosen);remaining=[c for c in remaining if chosen not in c]
assert all(selected.intersection(c) for c in clauses)
output=dict(status='EXACT_FIXED_POTENTIAL_COVER',potential_numerator=numerator,potential_denominator=29,reference_keys=len(reference_rows),states=len(pi),**dict(totals),distinct_clauses=len(clauses),mandatory_keys=len(forced),selected_keys=len(selected),selected_ids=sorted(selected),keys=[additional[i] for i in sorted(selected)],clauses=[dict(keys=c,edges=n,example=examples[c]) for c,n in sorted(clauses.items())],source_potential_sha256=sha(raw),seconds=time.monotonic()-start,scope='Finite fixed-potential exclusion selection. Selected keys remain numerical unless separately proved. Greedy selection is sufficient; optimality follows only if every selected key is mandatory.')
(HERE/f'data/selection{suffix}.json.gz').write_bytes(gzip.compress(json.dumps(output,separators=(',',':')).encode(),mtime=0));summary={k:v for k,v in output.items() if k not in ['keys','clauses','selected_ids']};(HERE/f'data/summary{suffix}.json').write_text(json.dumps(summary,indent=2)+'\n');print(summary,flush=True)
