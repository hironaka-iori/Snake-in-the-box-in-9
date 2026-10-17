import json, itertools, statistics as st, sys
from fractions import Fraction as F
bank=[e['vertex_sequence'] for e in json.load(open(sys.argv[1]))]
pairs=list(itertools.combinations(range(9),2))
allmin=[]; deep=[]; tot=[]
for s in bank[:40]:
    S=set(s); v=len(s)
    w={x:F(0) for x in s}; s0=0; dp=0
    for b in range(512):
        for i,j in pairs:
            if b>>i&1 or b>>j&1: continue
            Q=[b,b|1<<i,b|1<<j,b|1<<i|1<<j]
            if set(Q)&S: continue
            s0+=1
            nb={q^1<<k for q in Q for k in range(9) if k not in (i,j)}
            sel=nb&S
            if not sel: dp+=1; continue
            for x in sel: w[x]+=F(1,len(sel))
    al=[]
    for x in s:
        a=sum(1 for i,j in pairs if not({x^1<<i,x^1<<j,x^1<<i^1<<j}&S))
        al.append(float(a+2*w[x]))
    allmin.append(min(al[1:-1])); deep.append(dp/s0); tot.append(st.mean(al))
print("mean (alpha+2w) per vertex", st.mean(tot), "| min over internal vertices", min(allmin), st.mean(allmin))
print("fraction of empty squares with no selected neighbour (lost locally):", st.mean(deep))
