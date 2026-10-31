from pathlib import Path
import json,hashlib,collections
H=Path(__file__).resolve().parent
B=json.loads((H/'filtered_critical_edges.json').read_text());E={e['source_edge']:e for e in B};P=json.loads((H/'forbidden_patterns.json').read_text())
def canon(w):
 s=[];out=[]
 for a in w:
  if a not in s:s.append(a)
  out.append(s.index(a))
 return tuple(out)
for e in B:assert len(e['directions'])==9 and canon(e['directions'])==tuple(e['directions'])
D=sorted({tuple(tuple(E[t]['directions']) for t in p) for p in P});bylength=collections.Counter(map(len,D))
A=(0,1,2,0,3,2,4,3,5);Bword=(0,1,2,3,1,4,3,5,4)
AB=tuple(A if j%2==0 else Bword for j in range(9));BA=tuple(Bword if j%2==0 else A for j in range(9));assert AB in D and BA in D
geo=json.loads((H/'surviving_cycle_geometry_probe.json').read_text());C=geo['cycle_records'];assert len(C)==10 and [tuple(e['directions']) for e in C]==[A,Bword]*5
trials=0;results=[]
for pattern in D:
 first=list(pattern[0]);vs=[0]
 for a in first:vs.append(vs[-1]^(1<<a))
 assert all((a^b).bit_count()>1 for i,a in enumerate(vs) for j,b in enumerate(vs) if j>i+1)
 frontier=[(first,vs)]
 for wanted in pattern[1:]:
  nxt=[]
  for w,v in frontier:
   for a in range(9):
    trials+=1;ww=w+[a]
    if canon(ww[-9:])!=wanted:continue
    x=v[-1]^(1<<a)
    if all((x^z).bit_count()>1 for z in v[:-1]):nxt.append((ww,v+[x]))
  frontier=nxt
  if not frontier:break
 assert not frontier
 results.append({'length':len(pattern),'refuted':True})
(H/'direction_patterns_independent.json').write_text(json.dumps(D,separators=(',',':')))
r={'status':'PASS','edge_ID_patterns':len(P),'distinct_direction_word_patterns':len(D),'direction_patterns_by_length':dict(sorted(bylength.items())),'independent_full_nine_coordinate_trials':trials,'A':A,'B':Bword,'both_alternating_nine_word_patterns_present':True,'old_attaining_ten_cycle_alternates_AB':True,'scope':'directions only, count independent, geometry necessary for arbitrary Q9 snake','new_global_bound':None,'source_hashes':{n:hashlib.sha256((H/n).read_bytes()).hexdigest() for n in ['forbidden_patterns.json','filtered_critical_edges.json','direction_patterns_independent.json']}}
(H/'direction_generalization_review.json').write_text(json.dumps(r,indent=2));print(json.dumps(r,indent=2))
