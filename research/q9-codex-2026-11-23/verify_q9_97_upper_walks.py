"""Independently replay the six remaining single-root cases by geometric next-step enumeration."""
import gzip,itertools,json,subprocess,sys
from io import StringIO
from pathlib import Path
from verify_q9_97_donor_ports import path,check
def make(r,target=95):
    p=path(r['word']);root,=r['ports'];
    if p[-1]==root:p=p[::-1]
    check(p[0]==root,"port is not an end of the donor");c=r['cert'];dirs=[tuple(1<<j for j in ax) for ax in c['axes']]
    masks=list(map(sum,dirs));S=set(range(256))-set(p[1:]);prices={(m,v,z):a for m,v,z,a in c['weights']};scale=c['scale']
    check(r['added']==[] and sum(r['ends'])==1 and r['ends'][1-(root.bit_count()+target-1)%2]==1,'unsuitable branch')
    groups=[];sig={}
    for x in sorted(S):
        adj=[1<<d for d in range(8) if (x^(1<<d)) in S];scope=[x,*[x^d for d in adj]];options=[]
        for local in range(1<<len(scope)):
            if not local&1:
                if x!=root:options.append((local,0))
                continue
            z=sum(d for i,d in enumerate(adj) if local>>(i+1)&1)
            valence=z.bit_count()+int(x==root);color=1-x.bit_count()%2
            if valence!=2 and not (valence==1 and r['ends'][color]):continue
            options.append((local,scale-(1-2*(x.bit_count()%2))*c['balance_weight']-int(valence==1)*c['end_weights'][color]+sum(prices.get((m,x,z&m),0) for m in masks)))
            for m in masks:sig.setdefault((x,m),set()).add(z&m)
        groups.append((scope,options))
    for m,ds in zip(masks,dirs):
        for base in range(256):
            if base&m:continue
            vs=sorted(v for v in S if v&~m==base)
            if not vs:continue
            options=[]
            for bits in range(1<<len(vs)):
                on={v for i,v in enumerate(vs) if bits>>i&1}
                if root in vs and root not in on:continue
                near={v:{v^d for d in ds}&on for v in on}
                zs={v:sum(v^n for n in nb) for v,nb in near.items()}
                if any(z not in sig.get((v,m),set()) for v,z in zs.items()):continue
                unseen=set(on);forest=True
                while unseen:
                    comp=[unseen.pop()]
                    for v in comp:
                        new=unseen&near[v];unseen-=new;comp.extend(new)
                    if sum(len(near[v]) for v in comp)!=2*(len(comp)-1):forest=False;break
                if forest:options.append((bits,-sum(prices.get((m,v,z),0) for v,z in zs.items())))
            groups.append((vs,options))
    const=r['delta']*c['balance_weight']+sum(n*w for n,w in zip(r['ends'],c['end_weights']))
    check(const+sum(max(o[1] for o in opts) for _,opts in groups)==r['numerator'],'independent factors disagree')
    buf=StringIO();print(root,target,scale,const,r['numerator'],len(S),*sorted(S),len(groups),file=buf)
    for scope,opts in groups:
        print(len(scope),*scope,len(opts),file=buf)
        for bits,score in opts:print(bits,score,file=buf)
    return buf.getvalue(),p
def main():
    binary=sys.argv[1];cap=sys.argv[2] if len(sys.argv)>2 else '1000000000'
    target=int(sys.argv[3]) if len(sys.argv)>3 else 95
    check(3<=target<=95,"expected a target up to 95")
    stronger=dict(map(json.loads,gzip.open("q9_97_stronger_port_duals.jsonl.gz","rt")))
    if target in (93,94):
        stable=list(map(json.loads,gzip.open("q9_97_donor_port_duals.jsonl.gz","rt")))
        for i,r in stronger.items():stable[i]=r
        goal=97+target
        rows=[(i,r) for i,r in enumerate(stable) if (r["full"]==[1,1])==bool(goal%2) and r["bound"]>=goal and len(r["ports"])==1 and not r["added"]]
    else:
        check(target%2==1,"positive controls use odd upper counts")
        rows=[(i,r) for i,r in stronger.items() if r["bound"]>=192+int(r["full"]==[1,1])]
    if len(sys.argv)>4:
        wanted={int(v) for v in sys.argv[4].split(",")};rows=[(i,r) for i,r in rows if i in wanted]
        check({i for i,_ in rows}==wanted,"unknown branch index")
    for i,r in rows:
        s,p=make(r,target);out=subprocess.check_output([binary,cap],input=s,text=True).split()
        if out[0]=='FOUND':
            arm=list(map(int,out[2:]));q=p[::-1]+[256+v for v in arm]
            check(len(q)==98+target==len(set(q)) and all(((x^y).bit_count()==1)==(j==k+1) for k,x in enumerate(q) for j,y in enumerate(q) if j>k),'invalid witness')
        print(json.dumps(dict(index=i,upper_vertices=target,status=out[0],nodes=int(out[1]),witness=q if out[0]=="FOUND" else None)),flush=True)
if __name__=='__main__':main()
