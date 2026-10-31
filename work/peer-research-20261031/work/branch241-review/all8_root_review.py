from all8_cycles import templates
import itertools,json,math
from pathlib import Path
nbr=[sum(1<<(x^(1<<d)) for d in range(4)) for x in range(16)];pool=set()
for mask in range(1<<16):
 if mask.bit_count()!=8:continue
 vertices=[x for x in range(16) if mask>>x&1]
 if any((mask&nbr[x]).bit_count()!=2 for x in vertices):continue
 seen=1<<vertices[0];todo=[vertices[0]]
 while todo:
  x=todo.pop();more=nbr[x]&mask&~seen
  while more:
   bit=more&-more;more^=bit;seen|=bit;todo.append(bit.bit_length()-1)
 if seen==mask:pool.add(tuple(vertices))
assert pool==set(templates()) and len(pool)==168
layer_counts=[sum(all(x.bit_count()<=4-k for x in c) for c in pool) for k in range(6)]
assert layer_counts==[168,84,3,0,0,0]
total=math.comb(9,4)*sum(math.comb(5,k)*layer_counts[k] for k in range(6));assert total==77868
r={'independent_bitmask_Q4_templates':len(pool),'same_as_subagent_templates':True,'Q4_ball_layer_counts':layer_counts,'independent_B4_count':total,'formula':'C(9,4)*(168+5*84+10*3)'};Path(__file__).with_suffix('.json').write_text(json.dumps(r,indent=2));print(json.dumps(r,indent=2))
