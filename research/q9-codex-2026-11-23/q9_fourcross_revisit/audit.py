from pathlib import Path
from itertools import groupby
from collections import Counter
import json
D=Path(__file__).resolve().parent;B=D.parent/'q9_fourcross_new94';r=json.loads((D/'cases.json').read_text());N=[{v^1<<d for d in range(8)} for v in range(256)]
def induced(path,dim):
    assert len(set(path))==len(path) and all(0<=v<2**dim for v in path)
    for j,v in enumerate(path):
        for t in range(j):assert ((v^path[t]).bit_count()==1)==(t+1==j)
def logs(s):
    return [json.loads(l) for l in (D/s).read_text().splitlines()]
def read(file):
    arr=[]
    for l in file.read_text().splitlines():
        z=list(map(int,l.split()));p=z[5:5+z[4]];s=z[6+z[4]:];induced(p,8);induced(s,8);assert len(s)==z[5+z[4]] and not any((x^y).bit_count()<=1 for x in p for y in s);arr.append((p,s))
    return arr
def sym(a,b):return any(a==b[j:j+len(a)] or a[::-1]==b[j:j+len(a)] for j in range(len(b)-len(a)+1))
def norm(p,s):return tuple(sorted(p)),tuple(sorted(s))
allcases=[]
for kind in ('fullalt','highalt'):
    logs_= [dict(zip(z[::2],map(int,z[1::2]))) for l in (D/(kind+'.log')).read_text().splitlines() if (z:=l.split())]
    assert len(logs_)==730 and len({w['source'] for w in logs_})==730 and all(z['complete'] for z in logs_)
    for w in logs_:
        f=D/f"{kind}_{w['source']}.dat";sub=read(f) if f.exists() else [];assert len(sub)==w['distinct'];allcases+=sub
ground={norm(p,s) for p,s in allcases};indep=set()
for l in (D/'independent_sets.txt').read_text().splitlines():
    L,p,s=l.split();dec=lambda v:tuple(i for i,c in enumerate(v[::-1]) if c=='1');indep.add((dec(p),dec(s)))
assert ground==indep and len(ground)==5
for p,s in allcases:
    assert len(p)==93 and sym(r[0]['anchor'],p)
    spare=set(range(256))-set(p)-set.union(*(N[x] for x in p))
    def span(seq):
        return max([len(seq)-1]+[span(seq+[v]) for v in N[seq[-1]]&spare-set(seq) if all(w not in N[v] for w in seq[:-1])])
    assert max(span([x]) for x in spare)==3
proof={(w['i'],w['c']) for w in logs('fixedchecked.jsonl') if w.get('drat')}
assert proof=={(i,c) for i in range(5) for c in (0,1)}
joint=logs('replay54.jsonl');assert len(joint)==2 and all(z['verified'] for z in joint)
best={};witnesses=[]
for f in D.glob('*.paths'):
    for l in f.read_text().splitlines():
        z=list(map(int,l.split()));e=z[0];p=z[-e-1:];induced(p,9)
        g=[list(t) for _,t in groupby(p,lambda v:v>=256)];assert len(g)==5 and p[0]>=256 and p[-1]>=256
        main,s=sorted([g[1],g[3]],key=len,reverse=True);assert len(main)-1 in (92,93) and len(s)-1 in range(3,9)
        idx=0 if f.name=='control.paths' or f.name.startswith(('new184','real185','new186')) else 1
        assert sym(r[idx]['anchor'],main)
        entry=(e,f.name,p);best[f.name]=max(e,best.get(f.name,0))
        if idx==1:witnesses.append(entry)
if witnesses:
    e,name,p=max(witnesses);g=[list(t) for _,t in groupby(p,lambda v:v>=256)]
    (D/'best_seed0.json').write_text(json.dumps(dict(edges=e,seed=0,anchor_edges=24,pair_checks=len(p)*(len(p)-1)//2,components=[len(x)-1 for x in g],vertices=p,transitions=''.join(str((u^v).bit_length()-1) for u,v in zip(p,p[1:]))),indent=1))
print(json.dumps(dict(independent_lower_matches=len(ground),unique_main92=len({a for a,b in ground}),max_short_edges=3,fully_checked_upper_branches=len(proof),joint_proofs=len(joint),verified_best=best),indent=1))
