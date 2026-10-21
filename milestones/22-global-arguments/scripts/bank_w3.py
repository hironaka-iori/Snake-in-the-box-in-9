"""w_3 / w_4 statistics over all 131 bank snakes, and the alpha -> w_3 relation."""
import json, statistics as st
from subcube_census import census
from math import comb
import os; root=os.path.join(os.path.dirname(os.path.abspath(__file__)),'..','..','..')+'/'
bank=[e['vertex_sequence'] for e in json.load(open(root+'work/bank9.json'))]
def alpha(S,x):
    a=0
    for i in range(9):
        for j in range(i+1,9):
            if not({x^1<<i,x^1<<j,x^1<<i^1<<j}&S): a+=1
    return a
rows=[];byA={}
for s in bank:
    S=set(s); v=len(s)
    e3,w3,_=census(s,3); e2,w2,_=census(s,2)
    rows.append((v,e2,e3,float(min(w3[x] for x in s[1:-1])),float(sum(w3.values())/v)))
    for x in s[1:-1]:
        byA.setdefault(alpha(S,x),[]).append(float(w3[x]))
print('snakes',len(rows),'v',set(r[0] for r in rows))
print('empty squares: min %d max %d ; empty Q3: min %d max %d'%(min(r[1] for r in rows),max(r[1] for r in rows),min(r[2] for r in rows),max(r[2] for r in rows)))
print('min internal w3 over bank: %.4f ; mean w3 range %.3f..%.3f'%(min(r[3] for r in rows),min(r[4] for r in rows),max(r[4] for r in rows)))
print('alpha : count, min w3, mean w3')
for a in sorted(byA): print(a,len(byA[a]),round(min(byA[a]),3),round(st.mean(byA[a]),3))
