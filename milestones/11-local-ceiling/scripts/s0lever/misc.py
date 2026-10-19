import json, itertools, statistics as st, collections
import os
R=os.path.abspath(os.path.join(os.path.dirname(__file__), '../../../..')) + '/'
bank=[b['vertex_sequence'] for b in json.load(open(R+'work/bank9.json'))]
pairs=list(itertools.combinations(range(9),2))
s=bank[0]; S=set(s); v=len(s)
d=lambda a,b: bin(a^b).count('1')
alpha={x:sum(1 for i,j in pairs if not({x^1<<i,x^1<<j,x^1<<i^1<<j}&S)) for x in S}
d2={x:sum(1 for y in S if d(x,y)==2) for x in S}
print('alpha = 23 - d2 at path indices 2..v-3:', all(alpha[s[i]]==23-d2[s[i]] for i in range(2,v-2)))
D2=sum(d2.values())//2
s0=sum(1 for b in range(512) for i,j in pairs if not(b>>i&1 or b>>j&1) and not({b,b|1<<i,b|1<<j,b|1<<i|1<<j}&S))
T=sum(alpha.values())
print('s0', s0, '4602-29v+D2', 4602-29*v+D2, '| T', T, '10+23v-2D2', 10+23*v-2*D2)
# selected-neighbour counts of unselected vertices
for name,SS in [('bank0',S)]+[(f'adv{n}',set(json.load(open(R+f'milestones/11-local-ceiling/data/adversary{n}.json'))['S'])) for n in (208,224)]:
    c=collections.Counter(sum(1 for k in range(9) if q^1<<k in SS) for q in range(512) if q not in SS)
    print(name,'d(q) distribution over unselected q:',sorted(c.items()))
# ball sizes around k consecutive centres
for r in (3,4,5):
    for k in (1,3,4,5,6):
        sizes=[]
        for s in bank[:20]:
            for st0 in range(1,len(s)-k-1,7):
                cen=s[st0:st0+k]
                sizes.append(sum(1 for y in range(512) if min(d(y,c) for c in cen)<=r))
        print(f'r={r} k={k}: ball size mean {st.mean(sizes):.0f} max {max(sizes)} of 512')
