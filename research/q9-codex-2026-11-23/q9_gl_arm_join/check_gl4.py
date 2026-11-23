from bank import *
import subprocess
from collections import Counter
def walk(w):
    p=[0]
    for c in w:p.append(p[-1]^1<<int(c))
    return p
def canon(w):return min(normalize(w),normalize(w[::-1]))
def shape(S,d):
    nb={x:[x^1<<j for j in range(d) if x^1<<j in S] for x in S}
    ends=[x for x in S if len(nb[x])==1]
    if len(ends)!=2 or any(len(t)>2 for t in nb.values()):return
    v=ends[0];prev=None;axes=[]
    while True:
        nex=[x for x in nb[v] if x!=prev]
        if not nex:break
        x=nex[0];axes.append(str((v^x).bit_length()-1));v,prev=x,v
    return canon(''.join(axes)) if len(axes)==len(S)-1 else None
def generate(w):
    yield w
    p=walk(w)
    for k in range(4):
        x=p[-1]^1<<k
        if x not in p and all((x^y).bit_count()>1 for y in p[:-1]):yield from generate(w+str(k))
def groups(d):
    def step(tab):
        if len(tab)==1<<d:yield tab;return
        for v in range(1,1<<d):
            if v not in tab:yield from step(tab+[x^v for x in tab])
    return list(step([0]))
shapes=sorted({canon(w) for w in generate('') if len(w)>=2})
gs={i:groups(i) for i in [2,3,4]};hist=Counter()
for w in shapes:
    n=len(set(w));p=walk(w)
    expected={s for table in gs[n] if (s:=shape({table[v] for v in p},n))}
    actual={w}
    for k in range(1,n+1):
        z=subprocess.run([D/'parity_basis',str(k),'1000000','0','1'],input=w+' 0 0 0 0\n',text=True,capture_output=True,check=True)
        assert int(z.stderr.split()[-2])==0
        for line in z.stdout.splitlines():actual.add(line.split()[0])
    assert actual==expected,(w,expected-actual,actual-expected)
    hist[n]+=1
print(json.dumps(dict(shapes=hist,group_orders={n:len(v) for n,v in gs.items()})))
