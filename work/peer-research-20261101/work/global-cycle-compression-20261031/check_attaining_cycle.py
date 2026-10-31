from pathlib import Path
import json,hashlib
H=Path(__file__).resolve().parent;d=json.loads((H/'upstream_proved_analysis.json').read_text());words=[x['directions'] for x in d['cycle']]
def lift(phase,edges):
 out=words[phase][:];maps=[]
 for j in range(1,edges):
  w=words[(phase+j)%4];mp={}
  for symbol,actual in zip(w[:8],out[-8:]):
   assert symbol not in mp or mp[symbol]==actual
   mp[symbol]=actual
  assert len(mp)==6 and set(mp)==set(w) and len(set(mp.values()))==6
  out.append(mp[w[-1]]);maps.append(mp)
 return out,maps
def xorword(w):
 x=0
 for a in w:x^=1<<a
 return x
rows=[]
for phase in range(4):
 w,m=lift(phase,8);assert all(w[i]==w[i+8] for i in range(len(w)-8));first15=w[:15];assert xorword(first15).bit_count()==1 and xorword(w[:16])==0
 verts=[0]
 for a in first15:verts.append(verts[-1]^(1<<a))
 bad=[(i,j,(verts[i]^verts[j]).bit_count()) for i in range(len(verts)) for j in range(i+2,len(verts)) if (verts[i]^verts[j]).bit_count()<=1]
 assert bad==[(0,15,1)],bad
 rows.append({'phase':phase,'forbidden_7edge_pattern_ids':[d['cycle'][(phase+j)%4]['edge'] for j in range(7)],'first_16_literal_directions':w[:16],'unique_overlap_maps':m,'first15_xor':xorword(first15),'first16_xor':xorword(w[:16]),'nonconsecutive_distance_at_most_one_in_first15':bad})
out={'status':'PASS','source_sha256':hashlib.sha256((H/'upstream_proved_analysis.json').read_bytes()).hexdigest(),'phases':rows,'exclusion_scope':'7 consecutive edges following this exact four-edge cycle, all four phases; not individual edges, not other critical cycles'}
(H/'attaining_cycle_review.json').write_text(json.dumps(out,indent=2));print(json.dumps(out,indent=2))
