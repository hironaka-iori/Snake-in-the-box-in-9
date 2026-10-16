"""Untrusted alternative encoder with balanced cardinality counters and parity."""
from pathlib import Path
import runpy,json,sys
from itertools import combinations
d=runpy.run_path('work/lean/degree_cnf.py')
r=d['r'];h=d['h'];n=len(r);x=d['variables'];target=int(sys.argv[1]) if len(sys.argv)>1 else 82
clauses=[c for c in d['clauses'] if max(map(abs,c))<=2*n and not
         (len(c)==2 and all(v < -n for v in c))]
next_id=2*n+1
def new():
    global next_id
    k=next_id;next_id+=1;return k
def atmost(lits,k):
    if k>=len(lits):return
    if k<0:clauses.append([]);return
    def tree(a):
        if len(a)<=1:return a
        t=len(a)//2;left=tree(a[:t]);right=tree(a[t:])
        out=[new() for _ in range(min(k+1,len(a)))]
        for i in range(len(left)+1):
            for j in range(len(right)+1):
                if 0<i+j<=len(out):
                    clauses.append(([-left[i-1]] if i else [])+([-right[j-1]] if j else [])+[out[i+j-1]])
        return out
    out=tree(lits)
    clauses.append([-out[k]])
others=[]
for i,v in enumerate(r):
    e=n+1+i
    if v!=h:
        others.append(e)
        if (v.bit_count()^h.bit_count())%2 != (target-1)%2:clauses.append([-e])
atmost(others,1);clauses.append(others)
for parity in (0,1):
    side=[x[v] for v in r if v.bit_count()%2==parity]
    count=target//2+int(target%2==1 and parity==h.bit_count()%2)
    atmost(side,count);atmost([-v for v in side],len(side)-count)
# Every fully selected coordinate square would be a cycle.
for v in r:
    for a,b in combinations(range(9),2):
        if v&(1<<a) or v&(1<<b):continue
        q=[v,v^(1<<a),v^(1<<b),v^(1<<a)^(1<<b)]
        if all(w in x for w in q):clauses.append([-x[w] for w in q])
out=Path(f'work/lean/totalizer112_{target}')
out.with_suffix('.cnf').write_text(f'p cnf {next_id-1} {len(clauses)}\n'+''.join(' '.join(map(str,c))+' 0\n' for c in clauses))
out.with_suffix('.json').write_text(json.dumps({'clauses':clauses,'reasons':[None]*len(clauses),'variables':next_id-1}))
print('totalizer',target,next_id-1,len(clauses),flush=True)
