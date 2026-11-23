import sys,json,random
from search_q9_square_fiber_lift import lift
from itertools import combinations
coil=json.load(open("q9_coil_open_191_witness.json"))["cycle"]
word=[(a^b).bit_length()-1 for a,b in zip(coil,coil[1:]+coil[:1])]
def canon(w):
    m={};return bytes(m.setdefault(c,len(m)) for c in w)
walks=set();cuts=tuple(map(int,sys.argv[3:]))
for a,b in combinations(range(9),2):
    h=[c for c in word if c not in (a,b)];L=len(h)
    for i in range(L):
        for cut in cuts:
            z=(h+h)[i:i+L-cut]
            walks.add(min(canon(z),canon(z[::-1])))
data=sorted(walks);random.Random(6466).shuffle(data)
for w in data:
    p=[0]
    for c in w:p.append(p[-1]^(1<<c))
    st,out=lift(p,int(sys.argv[1]),int(sys.argv[2]))
    print(json.dumps([st,bytes(p).hex(),out],separators=(",",":")),flush=True)
    if out:break
