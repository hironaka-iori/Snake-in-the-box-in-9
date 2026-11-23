from pathlib import Path
from collections import Counter
import re
D=Path(__file__).resolve().parent;R=D.parent
def canon(w):
    d={};return ''.join(str(d.setdefault(c,len(d))) for c in w)
def path(w):
    a=[0]
    for c in w:a.append(a[-1]^1<<int(c))
    return a
N=[{v^1<<j for j in range(8)} for v in range(256)]
ws=(R/'q9_two_upper_free9495_20261121/reroutes/move/donors.words').read_text().split();bank=set()
files=[*R.glob('q8_*.words'),*R.glob('q8_*arms.txt'),*(R/'q9_fresh_mother_lifts_20261120').glob('q8_*words'),R/'q8_mother_search_20261120/mothers.tsv',R/'q9_two_upper_free9495_20261121/donors.words']
for file in files:
    for w in re.findall(r'(?<![0-9])[0-7]{92,100}(?![0-9])',file.read_text()):
        for L in (92,93):
            for j in range(len(w)-L+1):
                t=w[j:j+L];bank.add(min(canon(t),canon(t[::-1])))
print('screen',len(bank),flush=True)
allowed=[]
for w in sorted(bank):
    p=path(w);f=set(range(256))-set(p)-set.union(*(N[x] for x in p));short=[]
    for a in sorted(f):
        for b in N[a]&f:
            for c in (N[b]&f)-{a}:
                for d in (N[c]&f)-{a,b}-N[a]:
                    if d>a:short.append([a,b,c,d])
    if short:allowed.append((w,short))
print('lower geometric matches',len(allowed),Counter(len(w) for w,s in allowed),flush=True)
# Store one isometric donor most closely matching seed 0 for each candidate; all outputs are partial splices.
cands=[]
for n in range(88,12,-1):
    need={}
    for i,w in enumerate(ws):
        if i!=0:continue
        for k in range(len(w)-n+1):need.setdefault(canon(w[k:k+n]),[]).append((i,k))
    for w,short in allowed:
        for rev,t in enumerate((w,w[::-1])):
            for j in range(len(t)-n+1):
                for idx,k in need.get(canon(t[j:j+n]),[]):
                    cands.append((n,idx,k,w,short,rev,t,j))
    if cands:break
with (D/'spliced.dat').open('w') as fs,(D/'spliced_provenance.tsv').open('w') as pr:
    ct=0
    for n,i,k,w,short,rev,t,j in cands:
        for s in short:
            p=path(w);old=path(ws[i]);p=p[::-1] if rev else p;maps=dict(zip(t[j:j+n],ws[i][k:k+n]));taken=set(maps.values());un=[str(z) for z in range(8) if str(z) not in taken]
            for z in range(8):
                if str(z) not in maps:maps[str(z)]=un.pop()
            vmap=lambda v:sum(1<<int(maps[str(z)]) for z in range(8) if v>>z&1);shift=vmap(p[j])^old[k];conv=lambda v:vmap(v)^shift
            pp=[conv(v) for v in p];ss=[conv(v) for v in s];assert pp[j:j+n+1]==old[k:k+n+1]
            print(i,0,k,k+n,len(pp),*pp,len(ss),*ss,file=fs);print(i,k,n,w,rev,j,file=pr);ct+=1
            if ct>=100:break
        if ct>=100:break
print('largest inherited seed0 segment', cands[0][0] if cands else None,'variants',ct,flush=True)
