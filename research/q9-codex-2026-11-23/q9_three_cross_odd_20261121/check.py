import argparse,gzip,json,itertools,subprocess,tempfile
from pathlib import Path
from collections import Counter
D=Path(__file__).resolve().parent;R=D.parent
words=(R/'q8_catalogue_96_98.words').read_text().split()
def geometry(w):
    p=[0]
    for z in w:p.append(p[-1]^(1<<int(z)))
    assert len(set(p))==len(p) and all(((x^y).bit_count()==1)==(j+1==i) for i,x in enumerate(p) for j,y in enumerate(p[:i]))
    return sum(1<<v for v in p),p[-1],[(v|(0)) for v in range(256) if all((v^u).bit_count()>1 for u in p)]
G=[geometry(w) for w in words]
jobs=[(i,x) for i,(_,_,eligible) in enumerate(G) for x in eligible];assert len(jobs)==1496
def loadrows(names):
    out=[]
    for s in names:
        for l in (D/s).read_text().splitlines():
            try:r=json.loads(l)
            except ValueError:continue
            assert jobs[r['rank']]==(r['i'],r['x'])
            out.append(r)
    return out
def writecert(f,j,c):
    ax=[sum(1<<d for d in z) for z in c['axes']];ws=c['weights']
    print('C',j,c['scale'],*c['end_weights'],c['balance_weight'],len(ax),len(ws),*ax,file=f)
    for w in ws:print(*w,file=f)
def main():
    ap=argparse.ArgumentParser();ap.add_argument('action',choices=['check','transfer']);ap.add_argument('out');ap.add_argument('logs',nargs='+');ap.add_argument('--neighbors',type=int,default=5);args=ap.parse_args();rows=loadrows(args.logs)
    files=sorted({r['cert'] for r in rows});ids={v:i for i,v in enumerate(files)};certs={f:json.load(gzip.open(D/f,'rt')) for f in files}
    todo=[]
    if args.action=='check':todo=[(r['i'],r['x'],r['cert'],r['bound']) for r in rows]
    else:
        seeds={};good={(r['i'],r['x']) for r in rows if r['bound']<194*r['scale']}
        for r in rows:
            if '_a8.' in r['cert'] and r['bound']<195*r['scale']:seeds[r['cert']]=r
        for i,x in jobs:
            if (i,x) in good:continue
            def dist(r):
                k=r['i'];y=r['x'];v=r['bound']/r['scale']
                return (G[k][0]^G[i][0]).bit_count()+2*(G[k][1]!=G[i][1])+1*(x!=y)+4*((x^y).bit_count()%2)+0.4*(v-184)
            near=sorted(seeds.values(),key=dist)[:args.neighbors]
            todo.extend((i,x,r['cert'],None) for r in near)
    # Stream the integer certificates and tasks without requiring Python numerical packages.
    with tempfile.TemporaryFile('w+') as f:
        for j,p in enumerate(files):writecert(f,j,certs[p])
        for i,x,p,expected in todo:print('Q',ids[p],i,x,file=f)
        f.seek(0);proc=subprocess.Popen([str(D/'replay'),str(R/'q8_catalogue_96_98.words')],stdin=f,stdout=subprocess.PIPE,text=True)
        best={}
        for (i,x,p,want),line in zip(todo,proc.stdout,strict=True):
            j,a,b,val=map(int,line.split());assert (j,a,b)==(ids[p],i,x)
            if want is not None:assert val==want,(i,x,p,want,val)
            scale=certs[p]['scale'];r=dict(rank=jobs.index((i,x)),i=i,x=x,cert=p,scale=scale,bound=val)
            if (i,x) not in best or val/scale<best[i,x]['bound']/best[i,x]['scale']:best[i,x]=r
        assert proc.wait()==0 and len(best)==len({(t[0],t[1]) for t in todo})
    (D/args.out).write_text(''.join(json.dumps(v,separators=(',',':'))+'\n' for v in best.values()))
    print('checked',len(todo),'unique',len(best),'close193',sum(r['bound']<194*r['scale'] for r in best.values()),'close195',sum(r['bound']<196*r['scale'] for r in best.values()))
if __name__=='__main__':main()
