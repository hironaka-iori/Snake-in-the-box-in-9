"""Search near-path vertex domains. Every original vertex is optional; extras may lie far apart."""
import collections,itertools,json,random,subprocess,sys,os
from pathlib import Path
NB=[{v^(1<<a) for a in range(9)} for v in range(512)]
def valid(p):
    return len(p)==len(set(p)) and min(p)>=0 and max(p)<512 and all(((x^p[j]).bit_count()==1)==(j==i+1) for i,x in enumerate(p) for j in range(i+1,len(p)))
def test(domains,edges,cap):
    inp="".join(" ".join(map(str,sorted(D)))+"\n" for D in domains)
    p=subprocess.run([os.environ.get("Q9_HOST_ENGINE","/tmp/q9-domain-deletion-21"),str(edges),str(cap)],input=inp,text=True,capture_output=True,check=True)
    lines=p.stdout.splitlines();assert len(lines)==len(domains)
    for l,D in zip(lines,domains):
        t=l.split()
        if t[0]=="FOUND":
            w=list(map(int,t[1:]));assert len(w)==edges+1 and set(w)<=D and valid(w);yield t[0],w
        else:assert t[0] in ("NO","UNKNOWN");yield t[0],int(t[1])
def check():
    rng=random.Random(73601);cases=[]
    for i in range(100):
        D=set(rng.sample(range(16),rng.randrange(4,15)))
        if i%5==0:D|={x+256 for x in rng.sample(list(D),min(3,len(D)))}
        def longest(p):
            return max([len(p)-1]+[longest(p+[v]) for v in (NB[p[-1]]&D)-set(p) if not NB[v].intersection(p[:-1])])
        optimum=max(longest([x]) for x in D);cases.append((D,optimum))
    correct=0
    for e in range(2,11):
        for (s,v),(D,opt) in zip(test([D for D,_ in cases],e,200000),cases):assert (s=="FOUND")==(opt>=e) and s!="UNKNOWN";correct+=1
    ref=list(map(int,open("q9_odd_reference_vertices.txt").readline().split()));extra=set(rng.sample(sorted(set(range(512))-set(ref)),14))
    D=set(ref)|extra
    s,p=next(test([D],191,30000000));assert s=="FOUND" and valid(p)
    print(json.dumps(dict(compared=correct,small_domains=100,control_edges=len(p)-1,extra_points=len(extra))))
def run(trials,cap,salt):
    bank=[]
    for l in open("q9_new189_nearmisses.words"):
        loss,w=l.split();p=[0]
        for c in w:p.append(p[-1]^(1<<int(c)))
        idx={v:i for i,v in enumerate(p)};S=set(p)
        pairs=[(v,y) for i,v in enumerate(p) for y in NB[v]&S if idx[y]>i+1];assert len(pairs)==int(loss)
        hotspots=set(itertools.chain.from_iterable(pairs))|{p[0],p[-1]}
        extra=list(set(range(512))-S);features=[]
        for y in extra:
            hits=NB[y]&S;dd=min((x^y).bit_count() for x in hotspots)
            near=min((abs(idx[x]-idx[z]) for x in hits for z in hotspots),default=40)
            features.append((y,len(hits),dd,min(near,12)))
        bank.append((S,features,pairs))
    n2=sum(len(row[2])==2 for row in bank);rng=random.Random(salt)
    status=collections.Counter();nodes=0
    for batch in range(0,trials,24):
        domains=[];details=[]
        for t in range(batch,min(trials,batch+24)):
            k=rng.randrange(n2 if t%2==0 else len(bank));S,features,pairs=bank[k];size=int(os.environ.get("Q9_EXTRA_MIN",8))+(t%6)*int(os.environ.get("Q9_EXTRA_STEP",3))
            # Each draw mixes geometry-local and path-local repairs with remote bridge sites.
            mode=t%5
            rank=sorted((rng.expovariate(1)/(1+int(1<=h<=3)*3)/(1+(4-min(dd,4))*(mode!=0))/(1+(12-j)/2*(mode in (2,4))),x) for x,h,dd,j in features)
            extras={x for _,x in rank[:size]}
            if mode in (1,3):
                for x in list(extras)[:size//4]:
                    options=sorted(NB[x]-S-extras)
                    if options:extras.add(rng.choice(options))
            domains.append(S|extras);details.append((k,extras))
        for (s,val),(k,extras),D in zip(test(domains,192,cap),details,domains):
            status[s]+=1
            if s=="FOUND":
                print(json.dumps(dict(status=s,walk=k,extra=sorted(extras),path=val)),flush=True);return
            nodes+=val
        if batch%240==0 or batch+24>=trials:print(json.dumps(dict(trials=sum(status.values()),status=status,nodes=nodes)),flush=True)
if __name__=="__main__":
    if len(sys.argv)==1:check()
    else:run(*map(int,sys.argv[1:]))
