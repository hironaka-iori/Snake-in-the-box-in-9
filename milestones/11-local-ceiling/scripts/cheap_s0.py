import json, sys, itertools, statistics as st
pairs=list(itertools.combinations(range(9),2))
def analyse(S, label):
    S=set(S)
    e={x:0 for x in S}
    for b in range(512):
        for i,j in pairs:
            if b>>i&1 or b>>j&1: continue
            Q=[b,b|1<<i,b|1<<j,b|1<<i|1<<j]
            if set(Q)&S: continue
            for x in {q^1<<k for q in Q for k in range(9) if k not in (i,j)}&S: e[x]+=1
    al={x:sum(1 for i,j in pairs if not({x^1<<i,x^1<<j,x^1<<i^1<<j}&S)) for x in S}
    lum=st.mean(min(al[x],6) for x in S); cheap=st.mean(min(al[x],6)+2*e[x]/21 for x in S)
    f=lambda mu: 9214/(35+mu)-1
    print(f"{label}: mean lumped alpha {lum:.3f} -> floor {f(lum):.1f} | mean lumped alpha+2e/21 {cheap:.3f} -> floor {f(cheap):.1f} | min e {min(e.values())}")
analyse(json.load(open('data/adversary208.json'))['S'], 'adversary208')
analyse(json.load(open('data/adversary224.json'))['S'], 'adversary224')
b=json.load(open('../../work/bank9.json'))[0]['vertex_sequence']
analyse(b, 'bank snake 0')
