from pathlib import Path
from collections import defaultdict,Counter
import json
D=Path(__file__).resolve().parent;R=D.parent
def rel(w):
    d={};return ''.join(str(d.setdefault(c,len(d))) for c in w)
def key(w):return min(rel(w),rel(w[::-1]))
def path(w,v=0):
    p=[v]
    for c in w:p.append(p[-1]^(1<<int(c)))
    return p
def check(p):
    assert len(set(p))==len(p) and all(((x^y).bit_count()==1)==(j==i+1) for i,x in enumerate(p) for j,y in enumerate(p) if j>i)
def aw(w,x):
    return ''.join(str(x[c]) for c in w)
def oldset():
    old=(R/'q8_catalogue_96_98.words').read_text().split()
    return {key(w[i:i+n]) for w in old for n in (94,95) for i in range(len(w)-n+1)}
def generate():
    archived=oldset();knowncore=key(json.loads((R/'q9_frequent_95_audit.json').read_text())['core_word'])
    base=(R/'q9_fresh_mother_lifts_20261120/q8_novel1626_95_20.words').read_text().split()
    donors={key(w[i:i+n]) for w in base for n in (94,95) for i in range(len(w)-n+1)}-archived-{knowncore}
    refs={}; forests={}; direct=defaultdict(set)
    for n in (191,190,189):
        words=(R/f'q9_far189_spring_20261121/comparison{n}.words').read_text().split()
        for idx,w in enumerate(words):
            for axis in '012345678':
                if w.count(axis)!=2:continue
                for rev,z in enumerate((w,w[::-1])):
                    left,core,right=z.split(axis)
                    if not core or len(core)>114:continue
                    a=rel(core);k=key(core);perm={c:i for i,c in enumerate(dict.fromkeys(core+left+right))}
                    ca,cb=aw(left[::-1],perm),aw(right,perm)
                    code=path(a)[-1];u=path(ca);v=path(cb,code)
                    if len(core) in (94,95) and k not in archived and k!=knowncore and a==k:
                        donors.add(k);direct[k].add((ca,cb))
                        if k not in refs:refs[k]=(n,idx,int(axis),rev,ca,cb)
                    if len(u)+len(v)<86 or not code:continue
                    # Canonicalize the forest with the first port at zero; permute changed axes first.
                    seen=list(dict.fromkeys(ca+cb))+list('01234567')
                    labs=list(dict.fromkeys(int(c) for c in seen));m={s:i for i,s in enumerate([s for s in labs if code>>s&1]+[s for s in labs if not code>>s&1])}
                    f1=''.join(str(m[int(c)]) for c in ca);f2=''.join(str(m[int(c)]) for c in cb)
                    forests.setdefault((code.bit_count(),f1,f2),(n,idx,int(axis),rev))
    order=sorted(donors,key=lambda w:(w not in refs,-refs.get(w,(0,))[0],-len(w),w))
    assert not set(order)&archived and knowncore not in order
    (D/'donors.words').write_text('\n'.join(order)+'\n'); fs=sorted(forests,key=lambda a:(-len(a[1])-len(a[2]),a))
    with (D/'forests.dat').open('w') as f:
        for d,a,b in fs:print(d,a or '-',b or '-',*forests[d,a,b],file=f)
    with (D/'direct.dat').open('w') as f:
        for i,w in enumerate(order):
            for a,b in sorted(direct[w]):print(i,a or '-',b or '-',file=f)
    (D/'references.json').write_text(json.dumps({order.index(w):v for w,v in refs.items()},indent=1))
    print(dict(donors=len(order),lengths=Counter(map(len,order)),refs=len(refs),forests=len(fs),direct=sum(map(len,direct.values())),overlap96=len(set(order)&archived)))
if __name__=='__main__':generate()
