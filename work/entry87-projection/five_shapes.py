"""Independent direct count from five small shapes, with no optimization package."""
from collections import Counter
from itertools import combinations_with_replacement
from solve import paths

q=paths()[1]
chosen_bits=19
traces=[[]]
for i,v in enumerate(q):
    z=v&chosen_bits
    if i and z==(q[i-1]&chosen_bits):
        traces.append([])
    traces[-1].append(z)
shapes=({2},{3},{0,1},{0,19},{1,18})
for a,b in combinations_with_replacement(shapes,2):
    assert min((x^y).bit_count() for x in a for y in b)<=1
counts=Counter()
chosen=[]
for i in range(0,len(traces),2):
    for j,shape in enumerate(shapes):
        if shape<=set(traces[i]):
            counts[j]+=1
            chosen.append(i)
            break
assert [counts[i] for i in range(5)]==[8,12,9,1,3]
assert len(chosen)==33
small=sum(bool(set(traces[r])&{2,3}) for r in chosen)
assert small==20
assert any(traces[r]==[2] for r in chosen) and any(traces[r]==[3] for r in chosen)
assert sum(len(shapes[j])*counts[j] for j in range(5))==46
print("Five shape counts:",[counts[j] for j in range(5)])
print("Required words:",len(chosen),"minimum contact sites for this family:",2*len(chosen)-small)
