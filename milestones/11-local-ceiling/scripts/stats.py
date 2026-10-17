import json, itertools, statistics as st, sys
bank=[e['vertex_sequence'] for e in json.load(open(sys.argv[1]))]
pairs=list(itertools.combinations(range(9),2))
rows=[]
for s in bank:
    S=set(s); v=len(s)
    T=0; alphas=[]
    for x in s:
        a=0
        for i,j in pairs:
            y1,y2,y3=x^1<<i,x^1<<j,x^1<<i^1<<j
            if y1 not in S and y2 not in S and y3 not in S: a+=1
        alphas.append(a); T+=a
    s0=sum(1 for b in range(512) for i,j in pairs if not(b>>i&1 or b>>j&1)
           and not ({b,b|1<<i,b|1<<j,b|1<<i|1<<j}&S))
    ident=9214-35*v
    rows.append((v,T,s0,T+2*s0,ident,st.mean(alphas[1:-1]),min(alphas[1:-1])))
v,T,s0,L,R,ma,mn=rows[0]
print("v T s0 T+2s0 9214-35v meanalpha minalpha")
for r in rows[:5]: print(r)
print("avg T/v",st.mean(r[1]/r[0] for r in rows),"avg 2s0/v",st.mean(2*r[2]/r[0] for r in rows), "avg (T+2s0)/v", st.mean(r[3]/r[0] for r in rows))
print("needed (T+2s0)/v for v=197:", (9214-35*197)/197, " v=200:",(9214-35*200)/200)
