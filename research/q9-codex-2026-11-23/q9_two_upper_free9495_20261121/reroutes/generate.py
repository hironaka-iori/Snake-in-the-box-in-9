from pathlib import Path
from collections import Counter,defaultdict
import sys,json,random
D=Path(__file__).resolve().parent;sys.path.insert(0,str(D.parent))
from banks import path,key,oldset,check
rng=random.Random(20261121);W=(D.parent/'donors.words').read_text().split();arch=oldset()|{key(json.loads((D.parent.parent/'q9_frequent_95_audit.json').read_text())['core_word'])}
original=set(W);lines=(D.parent/'direct.dat').read_text().splitlines();rng.shuffle(lines)
donors={};seen=set();best={};N=[tuple(x^1<<j for j in range(8)) for x in range(256)];metrics=Counter()
def getword(p):return ''.join(str((u^v).bit_length()-1) for u,v in zip(p,p[1:]))
def save(q,a,b):
    w=getword(q);k=key(w)
    if k in arch or k in set(W[:16]) or (k in best and len(a)+len(b)<=best[k][0]):return
    if k not in donors:donors[k]=len(donors)
    check([256+x for x in a[::-1]]+q+[256+x for x in b]);best[k]=(len(a)+len(b),w,a,b);metrics['accepted']+=1
for line in lines:
    h,aa,bb=line.split();h=int(h);p=path(W[h]);al=path(aa.replace('-',''));bl=path(bb.replace('-',''),p[-1])
    for ltrim,rtrim in [(0,0),(2,0),(0,2),(4,4),(8,8)]:
        a=al[:max(1,len(al)-ltrim)];b=bl[:max(1,len(bl)-rtrim)];ban=set(a+b)-{p[0],p[-1]}
        for length in (3,4,5,6,7,8):
            for j in range(1,len(p)-length-1):
                left,right=p[j],p[j+length];shell=p[:j]+p[j+length+1:]
                tag=(h,left,right,length,tuple(sorted(ban)),j)
                if tag in seen:continue
                seen.add(tag);metrics['windows']+=1
                can=set(range(256))-ban-set(shell)
                for v in shell:can.difference_update(N[v])
                can|={left,right};run=[left];used={left}
                def rec(x,remaining):
                    if remaining==0:
                        if x==right and run!=p[j:j+length+1]:save(p[:j]+run+p[j+length+1:],a,b)
                        return
                    for y in N[x]:
                        if y not in can or y in used or (y^right).bit_count()>remaining-1 or ((y==right)!=(remaining==1)):continue
                        if any(z!=x and z in used for z in N[y]):continue
                        run.append(y);used.add(y);rec(y,remaining-1);used.remove(y);run.pop()
                rec(left,length)
out=[];seeds=[]
for k,i in donors.items():
    _,w,a,b=best[k];p=path(w);dx=p[-1];dirs=[d for z in (1,0) for d in range(8) if dx>>d&1==z];convert=lambda x:sum(((x>>old)&1)<<t for t,old in enumerate(dirs))
    out.append(w);seeds.append(' '.join(map(str,[i,len(p)+len(a)+len(b)-1,len(a),*map(convert,a),len(b),*map(convert,b)])))
(D/'donors.words').write_text('\n'.join(out)+'\n');(D/'survey.seeds').write_text('\n'.join(seeds)+'\n')
print(dict(metrics),dict(donors=len(out),outside_previous=sum(k not in original for k in donors),seed_histogram=Counter(int(l.split()[1]) for l in seeds)),flush=True)
