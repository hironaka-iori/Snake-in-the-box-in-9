from pathlib import Path
from collections import Counter
D=Path(__file__).resolve().parent;B=D.parent;old=(B/'q9_two_upper_free9495_20261121/reroutes/move/donors.words').read_text().split()
def rel(s):
    d={};return tuple(d.setdefault(c,len(d)) for c in s)
def path(w):
    p=[0]
    for c in w:p.append(p[-1]^1<<int(c))
    return p
def nonempty(p):return bool(p)
ws=[w for w in (B/'q8_catalogue_96_98.words').read_text().split() if len(w)>=97]
for sourced in ('q9_far189_spring_20261121/comparison189.words','q9_far189_spring_20261121/comparison190.words','q9_far189_spring_20261121/comparison191.words'):
    for q in (B/sourced).read_text().split():
        for z in set(q):
            for w in q.split(z):
                if len(w)>=97 and w not in ws:ws.append(w)
print('donors',len(ws),Counter(map(len,ws)),flush=True)
best={}
for n in range(92,12,-1):
    needles={}
    for i,w in enumerate(old):
        if i in best:continue
        for j in range(len(w)-n+1):
            needles.setdefault(rel(w[j:j+n]),[]).append((i,j))
    got={}
    for wi,w in enumerate(ws):
        for rev,x in enumerate((w,w[::-1])):
            for j in range(93-n):
                for i,k in needles.get(rel(x[j:j+n]),()):
                    cand=got.setdefault(i,[]);cand.append((i,k,n,wi,rev,j,x))
    best.update(got)
    if len(best)==2:break
with (D/'imports.dat').open('w') as f:
    for i,results in sorted(best.items()):
        print('source',i,'overlap',results[0][2],'placements',len(results))
        for i,k,n,wi,rev,j,x in results:
            print(i,k,n,wi,rev,j,x,file=f)
