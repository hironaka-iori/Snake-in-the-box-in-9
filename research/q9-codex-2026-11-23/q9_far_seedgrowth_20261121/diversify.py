from collections import Counter
import json,random
from prepare import D,R,NB,rootloss,emit
rng=random.Random(718327)
source=[];caps=0;transformed=Counter();seen=set();ranges=Counter()
def parse(l):
    a=list(map(int,l.split()));ln,e,cap,t,n=a[:5];h=set(a[5:5+n]);m=a[5+n];p=a[6+n:];assert len(p)==m
    return ln,e,cap,t,h,p
with (D/'retry.dat').open('w') as retry:
    for bank,log in [('knownroots','known'),('borrowed','borrowed'),('controls','control')]:
        inputs=[parse(l) for l in (D/(bank+'.dat')).open()]
        for l in (D/(log+'.log')).open():
            t=l.split()
            if t[0]=='ROW' and int(t[6]) and bank!='controls':
                i=int(t[1]);ln,e,cap,tag,h,p=inputs[i];emit(retry,ln,e,h,p,340000,tag);caps+=1
            if t[0]=='PATH':
                i=int(t[1]);ln,e,cap,tag,h,p=inputs[i];q=list(map(int,t[3:]))
                source.append((ln,h,q))
with (D/'grafted.dat').open('w') as out:
    for ln,h,q in source:
        for attempt in range(280):
            qq=q[::-1] if rng.randrange(2) else q
            l=rng.randrange(0,42);r=len(q)-rng.randrange(0,34);p=qq[l:r]
            if len(p)<102:continue
            width=rng.randrange(1,30);j=len(p)-width-1
            a,b=rng.sample(range(9),2);a=1<<a;b=1<<b
            pivot=p[j]
            z=p[:j+1]+[v^(a|b) if bool((v^pivot)&a)!=bool((v^pivot)&b) else v for v in p[j+1:]]
            if p==z: continue
            s=set(z);cnt=len(s-h)
            if not 5<=cnt<=15 or len(z)!=len(s):continue
            if sum(len(NB[v]&s) for v in z)!=2*(len(z)-1):continue
            lost=rootloss(z,h);emin=max(6,cnt,lost+193-len(h))
            if emin>15:continue
            e=rng.randint(emin,15)
            k=(ln,min(tuple(z),tuple(z[::-1])),e)
            if k in seen:continue
            seen.add(k);emit(out,ln,e,h,z,85000,400+attempt);transformed[cnt]+=1;ranges[e]+=1
print(json.dumps(dict(retries=caps,source_paths=len(source),graft_roots=len(seen),graft_outside=transformed,limits=ranges),indent=2))
