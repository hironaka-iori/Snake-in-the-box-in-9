"""Complete comparison model with only proof-supported local rules.
This builder reads no numerical-only count catalogue or share screen.
The arbitrary-snake graph assembly remains a separate proof obligation.
"""
from pathlib import Path
import collections,hashlib,json,sys,time
HERE=Path(__file__).resolve().parents[1];ROOT=HERE.parents[1]
sys.path.insert(0,str(ROOT/'work/solver_packages'))
import numpy as np
read=lambda p:json.loads(p.read_text(encoding='utf-8-sig'));sha=lambda b:hashlib.sha256(b).hexdigest();start=time.monotonic();enriched="--enriched" in sys.argv;tag="enriched-" if enriched else ""
sm=read(ROOT/'milestones/59-extended-share-window/extended/data/model.json');md=read(ROOT/'milestones/67-critical-family-charge/data/full-model.json')
geo=read(ROOT/'milestones/59-extended-share-window/data/geometry.json')['patterns']
ref=read(ROOT/'milestones/54-share-coverage/data/keys_235.json')['keys'];older=read(ROOT/'milestones/39-audited-bound-236/data/exclusion-catalogue.json')
# The four proved forward share inequalities and their reversals.
forward=[([0,1,2,3,1,4],[3,3,3,6,5],48),([0,1,2,3,4,5],[3,6,2,3,6],96),([0,1,2,0,3,4],[6,3,6,3,3],96),([0,1,2,3,4,5],[4,6,2,3,6],96)]
def canon(w):
 names=list(dict.fromkeys(w));return tuple(names.index(x) for x in w)
def encode(c):
 k=0
 for x in c:k=6*k+x-1
 return k
keys=sorted({min((canon(w),tuple(c)),(canon(w[::-1]),tuple(c[::-1]))) for w,c in [(w,[lo for lo,hi in bs]) for w,bs in ref]+older})
tables=collections.defaultdict(set)
for w,c in keys:
 tables[canon(w)].add(encode(c));tables[canon(w[::-1])].add(encode(c[::-1]))
rules=forward+[(canon(w[::-1]),c[::-1],b) for w,c,b in forward]
short_rules=[]
if enriched:
 for prior in ['47-critical-singleton-patterns','48-low-count-compatibility','49-six-direction-pair-catalogue']:
  short_rules += [dict(row,source=prior) for row in read(ROOT/f'milestones/{prior}/data/cases.json')]
 short_rules.append(dict(number=501,source='50-three-count-return',dirs=[0,1,2,3,4,0],positions=[1,4,5],kind='sum',cap=12))
code=np.arange(6**6,dtype=np.int32);C=np.stack([code//6**j%6+1 for j in range(5,-1,-1)],axis=1)
prefixes=[tuple(p) for p in md['prefixes']];sid={tuple(w):i for i,w in enumerate(sm['direction_shapes'])};B=6**5;N=sm['states'];arrays=collections.defaultdict(list)
for di,ds in enumerate(sm['extensions']):
 ps=sid[canon(ds[:8])];ts=sid[canon(ds[1:])];keep=np.ones(len(code),dtype=bool)
 for width in range(2,7):
  for offset in range(7-width):
   word=canon(ds[offset+2:offset+width+3])
   if word in tables:keep&=~np.isin((code//6**(6-offset-width))%6**width,list(tables[word]))
 if enriched:
  for row in short_rules:
   L=len(row['dirs']);positions=row.get('positions',[row.get('position')])
   for offset in range(10-L):
    piece=ds[offset:offset+L]
    for rev in [False,True]:
     if canon(piece[::-1] if rev else piece)!=tuple(row['dirs']):continue
     ps_local=[offset+(L-j if rev else j) for j in positions]
     if not all(3<=j<=8 for j in ps_local):continue
     vals=[C[:,j-3] for j in ps_local]
     if row['source'].startswith('47'):bad=vals[0]==1
     elif row['kind']=='sum':bad=(sum(vals)<=row['cap']) & np.logical_and.reduce([v<6 for v in vals])
     else:bad=np.logical_and.reduce([v<=cap for v,cap in zip(vals,row['caps'])])
     keep&=~bad
 ix=np.flatnonzero(keep);c=code[ix];cs=C[ix];credit=np.full(len(ix),geo[di]['share_lower'],dtype=np.int16)
 for w,counts,lower in rules:
  if canon(ds[-6:])==tuple(w):
   hit=c%6**5==encode(counts);credit[hit]=np.maximum(credit[hit],lower)
 for q,prefix in enumerate(prefixes):
  if q and md['compatible_shapes'][q]!=ps:continue
  hist=prefix+(di,);choices=[j for j,p in enumerate(prefixes) if p and len(p)<=len(hist) and hist[-len(p):]==p];nq=max(choices,key=lambda j:len(prefixes[j])) if choices else 0
  if nq:assert md['compatible_shapes'][nq]==ts
  lower=credit.copy();accept=np.ones(len(c),dtype=bool)
  for pat in md['patterns']:
   if len(hist)<3 or hist[-3:]!=tuple(pat['signature']):continue
   hit=np.ones(len(c),dtype=bool)
   for k,cap in pat['caps'].items():hit&=cs[:,int(k)]<=cap
   if pat['mode']=='exclusion':accept&=~hit
   else:lower=np.maximum(lower,pat['geometric_lower']);lower[hit]=np.maximum(lower[hit],pat['lower'])
  cc=c[accept];w=120*cs[accept,-1].astype(np.int64)+lower[accept]
  for name,data in [('U',(ps*B if q==0 else N+(q-1)*B)+cc//6),('V',(ts*B if nq==0 else N+(nq-1)*B)+cc%B),('weight',w),('direction',np.full(len(cc),di)),('count_code',cc),('history',np.full(len(cc),q))]:arrays[name].append(data.astype(np.int32))
a={k:np.concatenate(v) for k,v in arrays.items()};np.savez_compressed(HERE/f'build/{tag}graph.npz',**a)
out=dict(states=md['states'],edges=len(a['U']),reference_keys=len(keys),additional_proved_rules=short_rules,forward_rules=forward,patterns=md['patterns'],prefixes=md['prefixes'],compatible_shapes=md['compatible_shapes'],arrays_sha256={k:sha(v.tobytes()) for k,v in a.items()},seconds=time.monotonic()-start,scope='Local rules supported by recorded Lean proofs. No numerical-only count exclusions or shares. Full normalization/history assembly and complete Lean potential checking remain pending.')
(HERE/f'data/{tag}model.json').write_text(json.dumps(out,indent=2)+'\n');print({k:v for k,v in out.items() if k not in ['patterns','prefixes','compatible_shapes','arrays_sha256','forward_rules','additional_proved_rules']},flush=True)
