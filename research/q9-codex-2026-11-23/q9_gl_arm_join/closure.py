from pathlib import Path
import json,subprocess
D=Path(__file__).resolve().parent
raw=(D/'sources.txt').read_text().split()
def read(fn):
    return [(k,int(i),int(u),int(v),int(orig)) for z in fn.read_text().splitlines() for k,i,u,v,orig in [z.split()]]
base=read(D/'transformed.txt');provenance={w:[1,raw[i],u,v] for w,i,u,v,orig in base if u and w not in raw};all_shapes={w:(i,u,v,orig) for w,i,u,v,orig in base}
work=sorted(provenance);covered=set(raw);report=[];roundno=2
while work and roundno<=12 and len(covered)+len(work)<=30000:
    with (D/f'wave{roundno}.log').open('w') as err:
        z=subprocess.run([D/'transform','9'],input='\n'.join(work)+'\n',capture_output=False,stdout=subprocess.PIPE,stderr=err,text=True,check=True)
    new=set()
    for line in z.stdout.splitlines():
        w,i,u,v,orig=line.split();i,u,v=map(int,(i,u,v))
        if w not in all_shapes:
            new.add(w);provenance[w]=[roundno,work[i],u,v];all_shapes[w]=(-1,u,v,0)
    report.append([roundno,len(work),len(new)]);covered.update(work);work=sorted(new);roundno+=1
with (D/'closure.txt').open('w') as f:
    for w,(i,u,v,orig) in sorted(all_shapes.items()):print(w,i,u,v,orig,file=f)
(D/'lineage.json').write_text(json.dumps(provenance))
(D/'closure_stats.json').write_text(json.dumps(dict(first=len(base),sources=len(raw),steps=report,pending=len(work),total=len(all_shapes))))
print(report,'pending',len(work),'total',len(all_shapes))
