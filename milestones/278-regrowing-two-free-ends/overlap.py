"""Transfer checked forbidden intervals to every archived path containing an isometric copy."""
from argparse import ArgumentParser
from collections import Counter,defaultdict
from hashlib import sha256
from archive import HERE,input_paths,read,write
from grow import independent_check

def transitions(p):
    return bytes((v^w).bit_length()-1 for v,w in zip(p,p[1:]))
def normal(w):
    order=bytes(dict.fromkeys(w))
    return w.translate(bytes.maketrans(order,bytes(range(len(order)))))
def shape(w):
    return min(normal(w),normal(w[::-1]))

def evidence(paths,ignore=None):
    by=defaultdict(dict)
    def include(p,ident,filename):
        w=shape(transitions(p));assert sha256(w).hexdigest()==ident
        by[len(w)].setdefault(w,(ident,filename))
    for f in sorted(HERE.glob("cases-*-cube.json")):
        tag=f.stem[6:];rf=HERE/("replay-"+tag+".json")
        if not rf.exists():continue
        other=read(rf.name)["results"]
        minimum,width=map(int,tag.split("-")[:2])
        for k,v in read(f.name).items():
            if v["closed"] and other[k]["complete"] and v["maximum_seen"]<192:
                assert other[k]["histogram"]==v["histogram"]
                p=paths[v["source"]];include(p[width:len(p)-width],k,f.name)
    for pattern in ("target-*-192.json","window-*-192.json"):
        for f in sorted(HERE.glob(pattern)):
            if f.name==ignore:continue
            bit=f.stem.split("-");value=int(bit[2])
            for k,r in read(f.name).items():
                if len(r["records"])!=2 or any(d["status"]!="excluded" for d in r["records"].values()):continue
                p=paths[r["source"]]
                core=p[value:len(p)-value] if bit[0]=="target" else p[r["offset"]:r["offset"]+value+1]
                include(core,k,f.name)
    native_hashes={f.name:sha256(f.read_bytes()).hexdigest() for f in HERE.glob("TwoTail*.cs")}
    for f in sorted(HERE.glob("paired-*-192.json")):
        if f.name==ignore:continue
        length=int(f.stem.split("-")[2])
        for k,r in read(f.name).items():
            if r["status"]!="excluded":continue
            assert r["left_exact"] and r["right_exact"]
            assert r["source_sha256"]==native_hashes[r.get("source_file","TwoTailJoin.cs")]
            p=paths[r["source"]];i=r["offset"]
            include(p[i:i+length+1],k,f.name)
    return by

def occurrences(word,by):
    hits=[]
    for n,cert in by.items():
        for i in range(len(word)-n+1):
            x=cert.get(shape(word[i:i+n]))
            if x is not None:hits.append((i,i+n,x[0],x[1]))
    return hits

def reduced(hits):
    # Discard any interval containing a shorter forbidden interval. The surviving
    # left and right endpoints are both monotone in increasing path order.
    results=[];upper=10**9
    for h in sorted(hits,key=lambda h:(-h[0],h[1])):
        if h[1]<upper:results.append(h);upper=h[1]
    return results[::-1]

def literal_isometry(p,q):
    if len(p)!=len(q):return False
    for s in (p,p[::-1]):
        mapping={}
        for a,b,u,v in zip(s,s[1:],q,q[1:]):
            k=a^b;w=u^v
            if mapping.setdefault(k,w)!=w:break
        else:
            if len(set(mapping.values()))!=len(mapping):continue
            if all(q[0]^sum(w for k,w in mapping.items() if (v^s[0])&k)==z for v,z in zip(s,q)):return True
    return False

def plan(args):
    from target import solve_data
    paths=dict(input_paths());tag="window-%d-%d-192"%(args.minimum,args.length)
    name="plan-"+tag+".json"
    if not (HERE/name).exists():
        known=evidence(paths,tag+".json")
        scopes={};counts=Counter()
        for label,path in paths.items():
            if len(path)-1<args.minimum:continue
            word=transitions(path);hits=reduced(occurrences(word,known))
            for i in range(len(path)-args.length):
                j=i+args.length;counts["total"]+=1
                if any(i<=start and stop<=j for start,stop,*_ in hits):
                    counts["already_excluded"]+=1;continue
                key=shape(word[i:j]).hex()
                row=scopes.setdefault(key,dict(source=label,offset=i,occurrences=0));row["occurrences"]+=1
        write(name,dict(counts=counts,scopes=scopes))
    scopes=read(name)["scopes"];data={}
    for key,r in scopes.items():
        p=paths[r["source"]];i=r["offset"];q=p[i:i+args.length+1]
        assert shape(transitions(q)).hex()==key
        data[bytes.fromhex(key)]=dict(**r,a=q[:1],m=q[1:-1],b=q[-1:])
    if not data:print("All windows already excluded.");return
    args.target=192;args.only=None
    solve_data(args,data,tag)

def summarize():
    paths=dict(input_paths());by=evidence(paths)
    reps={}
    for n,m in by.items():
        for w,(k,filename) in m.items():reps[k]=w
    outcomes={};dist=defaultdict(Counter);counts=Counter();tot=0
    for label,p in paths.items():
        w=transitions(p);n=len(w)
        hits=reduced(occurrences(w,by));bound=-1;example=None
        for start in range(n+1):
            stop=min((hi-1 for lo,hi,*_ in hits if lo>=start),default=n)
            if stop-start>bound:bound=stop-start;example=[start,stop]
        # Reconstruct the source interval directly and compare its literal image.
        for lo,hi,k,filename in hits:
            core=[0]
            for dim in reps[k]:core.append(core[-1]^(1<<dim))
            assert literal_isometry(core,p[lo:hi+1])
        for i in range(n-bound):
            assert any(i<=lo and hi<=i+bound+1 for lo,hi,*_ in hits)
        assert not any(example[0]<=lo and hi<=example[1] for lo,hi,*_ in hits)
        outcomes[label]=dict(edges=n,bound=bound,longest_interval_avoiding_certificates=example,cover=hits)
        dist[n][bound]+=1;counts[n]+=1;tot+=len(hits)
    result=dict(certificates_by_length={n:len(v) for n,v in sorted(by.items())},
        archive_counts=counts,upper_bound_histograms=dist,
        maximum_shared_edges={n:max(h) for n,h in dist.items()},cover_intervals_verified=tot,paths=outcomes)
    write("consecutive-overlap.json",result)
    print("Maximum possible consecutive overlap",result["maximum_shared_edges"],"by source length")
    print("Bound histograms",dict(dist),"certificates",result["certificates_by_length"],"literal inclusions",tot)
if __name__=="__main__":
    ap=ArgumentParser();ap.add_argument("action",choices=["search","summarize"]);ap.add_argument("--length",type=int,default=165)
    ap.add_argument("--minimum",type=int,default=191);ap.add_argument("--budget",type=int,default=30000)
    ap.add_argument("--engine",choices=["Target","TargetReplay"]);args=ap.parse_args()
    if args.action=="search":plan(args)
    else:summarize()


