"""Rebuild the selected-exclusion graph and validate every mandatory-key witness."""
from pathlib import Path
from fractions import Fraction
import collections,gzip,hashlib,json,sys,time
HERE=Path(__file__).resolve().parents[1];ROOT=HERE.parents[1]
sys.path.insert(0,str(ROOT/'work/solver_packages'))
import numpy as np
read=lambda p:json.loads(p.read_text(encoding='utf-8-sig'));sha=lambda b:hashlib.sha256(b).hexdigest();start=time.monotonic();numerator=int(sys.argv[1]) if len(sys.argv)>1 else 14392;suffix='' if numerator==14392 else '-'+str(numerator)
selection=json.loads(gzip.decompress((HERE/f'data/selection{suffix}.json.gz').read_bytes()));selected=set(selection['selected_ids'])
P=ROOT/'milestones/68-proof-dependency-pressure';md=read(P/'data/share-clean-model.json');sm=read(ROOT/'milestones/59-extended-share-window/extended/data/model.json')
additional=json.loads(gzip.decompress((P/'data/count-subsumption.json.gz').read_bytes()))['needed']
reference=read(ROOT/'milestones/54-share-coverage/data/keys_235.json')['keys']
geometry=read(ROOT/'milestones/59-extended-share-window/data/geometry.json')['patterns']
rules=read(ROOT/'milestones/57-replacement-share-family/combined/data/model.json')['share_rules'];rules=[r for r in rules if r.get('status')!='NUMERICAL_ONLY']
raw=gzip.decompress((P/'data/share-clean-potential.i64.gz').read_bytes());assert sha(raw)==selection['source_potential_sha256'];pi=np.frombuffer(raw,dtype='<i8')
def canon(w):
 lookup={};return tuple(lookup.setdefault(d,len(lookup)) for d in w)
def number(c):
 n=0
 for x in c:n=6*n+x-1
 return n
def make_lookup(rows):
 lookup=collections.defaultdict(dict)
 for i,(w,c) in enumerate(rows):
  for ww,cc in [(w,c),(w[::-1],c[::-1])]:lookup[canon(ww)][number(cc)]=i
 return lookup
reference_rows=[(w,[b[0] for b in bounds]) for w,bounds in reference]
reference_rows += read(ROOT/'milestones/39-audited-bound-236/data/exclusion-catalogue.json')
reference_rows=sorted({min((canon(w),tuple(c)),(canon(w[::-1]),tuple(c[::-1]))) for w,c in reference_rows})
base=make_lookup(reference_rows);extra=make_lookup(additional)
assert selection['keys']==[additional[i] for i in sorted(selected)]
singletons={r['keys'][0]:r for r in selection['clauses'] if len(r['keys'])==1}
assert selected==set(singletons) and all(selected.intersection(r['keys']) for r in selection['clauses'])
shapes={tuple(w):i for i,w in enumerate(sm['direction_shapes'])};B=6**5;N=sm['states'];prefixes=[tuple(x) for x in md['prefixes']]
def next_state(q,di):
 hist=prefixes[q]+(di,)
 matches=[i for i,x in enumerate(prefixes) if x and hist[-len(x):]==x]
 return max(matches,key=lambda i:len(prefixes[i])) if matches else 0
# The transition list is independently enumerated as induced coordinate words.
def words(ds=(),vertices=(0,)):
 if len(ds)==9:yield ds;return
 for d in range(min(9,max(ds,default=-1)+2)):
  v=vertices[-1]^(1<<d)
  if v in vertices or any((v^u).bit_count()==1 for u in vertices[:-1]):continue
  yield from words(ds+(d,),vertices+(v,))
assert list(words())==[tuple(w) for w in sm['extensions']]
def lookup_occurrences(ds,counts,table):
 hits=set()
 for offset in range(5):
  for width in range(2,7-offset):
   sub=canon(ds[offset+2:offset+3+width]);id=table.get(sub,{}).get(number(counts[offset:offset+width]))
   if id is not None:hits.add(id)
 return hits
for k,row in singletons.items():
 e=row['example'];di,q,code=e['direction'],e['history'],e['count_code'];ds=sm['extensions'][di]
 counts=[code//6**j%6+1 for j in range(5,-1,-1)];ps=shapes[canon(ds[:8])];ts=shapes[canon(ds[1:])]
 assert q==0 or md['compatible_shapes'][q]==ps
 assert not lookup_occurrences(ds,counts,base) and lookup_occurrences(ds,counts,extra)=={k}
 lo=geometry[di]['share_lower']
 for rule in rules:
  if canon(ds[-6:])==tuple(rule['directions']) and counts[-5:]==rule['counts']:lo=max(lo,rule['lower'])
 hist=prefixes[q]+(di,)
 for pat in md['patterns']:
  if len(hist)<3 or hist[-3:]!=tuple(pat['signature']):continue
  hit=all(counts[int(j)]<=cap for j,cap in pat['caps'].items())
  if pat['mode']=='exclusion':assert not hit
  else:lo=max(lo,pat['geometric_lower'],pat['lower'] if hit else 0)
 nq=next_state(q,di);u=(ps*B if q==0 else N+(q-1)*B)+code//6;v=(ts*B if nq==0 else N+(nq-1)*B)+code%B
 slack=29*(120*counts[-1]+lo)+int(pi[u])-int(pi[v])-numerator
 assert slack==e['slack'] and slack<0
# Rebuild all retained transitions without importing the selector's implementation.
code=np.arange(6**6,dtype=np.int32);counts=np.stack([code//6**j%6+1 for j in range(5,-1,-1)],axis=1)
arrays=collections.defaultdict(list);candidate=negative=0
for q,prefix in enumerate(prefixes):
 for di,ds in enumerate(sm['extensions']):
  ps=shapes[canon(ds[:8])];ts=shapes[canon(ds[1:])]
  if q and md['compatible_shapes'][q]!=ps:continue
  forbidden=np.zeros(len(code),dtype=bool);chosen=np.zeros(len(code),dtype=bool)
  for offset in range(5):
   for width in range(2,7-offset):
    word=canon(ds[offset+2:offset+3+width]);subcode=(code//6**(6-offset-width))%6**width
    if word in base:forbidden|=np.isin(subcode,list(base[word]))
    if word in extra:chosen|=np.isin(subcode,[c for c,k in extra[word].items() if k in selected])
  lo=np.full(len(code),geometry[di]['share_lower'],dtype=np.int16)
  for rule in rules:
   if canon(ds[-6:])==tuple(rule['directions']):
    ix=code%6**5==number(rule['counts']);lo[ix]=np.maximum(lo[ix],rule['lower'])
  hist=prefix+(di,)
  for pat in md['patterns']:
   if len(hist)<3 or hist[-3:]!=tuple(pat['signature']):continue
   hit=np.ones(len(code),dtype=bool)
   for k,cap in pat['caps'].items():hit&=counts[:,int(k)]<=cap
   if pat['mode']=='exclusion':forbidden|=hit
   else:lo=np.maximum(lo,pat['geometric_lower']);lo[hit]=np.maximum(lo[hit],pat['lower'])
  nq=next_state(q,di)
  U=(ps*B if q==0 else N+(q-1)*B)+code//6;V=(ts*B if nq==0 else N+(nq-1)*B)+code%B
  weight=120*counts[:,-1].astype(np.int64)+lo;slack=29*weight+pi[U]-pi[V]-numerator
  candidate+=int((~forbidden).sum());negative+=int(((slack<0)&~forbidden).sum())
  keep=~(forbidden|chosen);assert np.all(slack[keep]>=0)
  for name,values in [('U',U[keep]),('V',V[keep]),('weight',weight[keep]),('count_code',code[keep]),('history',np.full(int(keep.sum()),q)),('direction',np.full(int(keep.sum()),di))]:arrays[name].append(values.astype(np.int32))
assert candidate==selection['candidate_edges'] and negative==selection['violating_edges']
a={k:np.concatenate(v) for k,v in arrays.items()};np.savez_compressed(HERE/f'build/selected{suffix}-graph.npz',**a)
report=dict(status='PASS',reference_keys=len(reference_rows),states=len(pi),candidate_edges=candidate,negative_edges=negative,retained_edges=len(a['U']),selected_keys=len(selected),mandatory_witnesses=len(singletons),unique_least_cover_for_fixed_potential=True,potential_mean=str(Fraction(numerator,29)),potential_range=int(max(pi)),conditional_bound=str(Fraction(1098960*29+8*numerator+int(max(pi)),numerator+4200*29)),arrays_sha256={k:sha(v.tobytes()) for k,v in a.items()},seconds=time.monotonic()-start,scope='Independent full graph reconstruction and verification of every mandatory-key witness. Least-cover claim fixes the candidate basis, graph and potential. Selected keys still need proofs; no global snake bound.')
(HERE/f'data/verification{suffix}.json').write_text(json.dumps(report,indent=2)+'\n');print(report,flush=True)
