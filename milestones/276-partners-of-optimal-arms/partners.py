"""Construct opposite arms, then search unrestricted complements and replay their certificates."""
from argparse import ArgumentParser
from collections import Counter,defaultdict
from hashlib import sha256
from pathlib import Path
from tempfile import TemporaryDirectory
import os,subprocess,sys
from inputs276 import HERE,MS,canonical,read,save,valid,path_of

def cases():
    data=read(HERE/"input-arms.json")
    result={}
    for root,rec in data["known_endpoints"].items():
        result[root]=dict(shape=data["reference_shape"],parent=rec["parent"],old=rec)
    extra={}
    for f in sorted([*HERE.glob("anchors-*.json"),*HERE.glob("site-neighbours-*.json")]):
        extra.update(read(f)["shapes"])
    dist=HERE/"site-distance.json"
    if dist.exists():
        for row in read(dist).values():
            for p in row["paths"]:extra.setdefault(canonical(p),dict(path=p))
    for s,r in extra.items():
        if s==data["reference_shape"]:continue
        p=path_of(bytes.fromhex(s));assert len(p)==99 and valid(p,8)
        for d,q in enumerate((p,p[::-1])):
            a=[v^q[0] for v in q]; label=sha256(bytes(a)).hexdigest()
            result[label]=dict(shape=s,parent=a,old=dict(lower=len(a),upper=len(a)+98,partner=[0]))
    return result

def witness(p,b):
    assert p[0]==b[0]==0 and set(p)&set(b)=={0}
    q=p[::-1]+[256+v for v in b];return dict(parent=p,partner=b,joined=q,edges=len(q)-1,pairs=valid(q,9))

def construct(roots,steps,passes):
    f=HERE/"placements.json";out=read(f) if f.exists() else {}
    with TemporaryDirectory(prefix="q9-build276-") as t:
        exe=Path(t)/"JoinedSearch.exe"
        csc=Path(os.environ["WINDIR"])/"Microsoft.NET/Framework64/v4.0.30319/csc.exe"
        subprocess.run([str(csc),"/nologo","/optimize+","/out:"+str(exe),str(MS/"265-joint-arm-regrowth/JoinedSearch.cs")],
                       capture_output=True,check=True)
        for k,r in roots.items():
            p=r["parent"];old=r["old"]
            rec=out.setdefault(k,dict(best=witness(p,old["partner"]),runs=[]))
            assert rec["best"]["parent"]==p
            for pass_id in range(passes):
                salt=276000+int(sha256(k.encode()).hexdigest()[:5],16)+37*pass_id
                if any(s["salt"]==salt and s["steps"]==steps for s in rec["runs"]):continue
                b=rec["best"]["partner"]
                entry="".join(",".join(map(str,a))+"\n" for a in [p,b])
                lines=subprocess.run([str(exe),str(salt),str(steps),"fixed"],input=entry,text=True,capture_output=True,check=True).stdout.splitlines()
                A,B=[list(map(int,line.split(","))) for line in lines[:2]];assert p==A and len(B)>=len(b)
                w=witness(p,B);rec["best"]=w;rec["runs"].append(dict(salt=salt,steps=steps,from_edges=len(p)+len(b)-1,
                    edges=w["edges"],counters=list(map(int,lines[-1].split(",")))))
                save(f,out);print("Construction",k[:8],steps,pass_id,w["edges"],flush=True)
                if w["edges"]>=192:save(HERE/"candidate-192.json",w);return
    save(f,out)

def older(target=192):
    direct=read(MS/"249-long-parent-joins/direct98.json");audit=read(MS/"249-long-parent-joins/audit98.json")
    source="milestones/249-long-parent-joins/direct98.json"
    assert sha256((MS.parent/source).read_bytes()).hexdigest()==audit["inputs"][source]
    cuts=defaultdict(list)
    for row in direct["records"]:
        if row["status"]!="excluded" or row["length"]+99>target:continue
        assert row["checker"].startswith("VERIFIED UNSAT") and sha256((MS/"249-long-parent-joins"/row["proof"]).read_bytes()).hexdigest()==row["gzip_sha256"]
        cuts[str(row["root"])].append((row["length"]+99,tuple(row["prefix"])))
    return cuts

def legal(p,prefix):
    return [v for d in range(8) for v in [prefix[-1]^(1<<d)] if v not in p and v not in prefix and
            all((v^a).bit_count()!=1 for a in prefix[:-1])]

def hunt():
    sys.path.insert(0,str(MS/"271-rebuilt-historical-partners"));sys.path.insert(0,str(MS/"269-archived-93-arms"))
    import hunt as h
    return h

def mask(p,prefix):
    last=prefix[-1]
    return {v^last for v in range(256) if v in p[1:] or (v!=last and any((v^w).bit_count()<=1 for w in prefix[:-1]))}

def search(roots,args):
    h=hunt();h.rebuild.model=h.deficit.model
    prev=older(args.target)
    f=HERE/("queries-%d.json"%args.target);out=read(f) if f.exists() else {}
    with TemporaryDirectory(prefix="q9-query276-") as t:
        tmp=Path(t);tools=h.rebuild.masks.compilers(tmp)
        for k,r in roots.items():
            if args.roots and k not in args.roots or r["old"]["upper"]<args.target:continue
            p=r["parent"];dest=out.setdefault(k,{})
            cuts={pref for target,pref in prev[k] if target<=args.target}
            for qfile in HERE.glob("queries-*.json"):
                if int(qfile.stem.split("-")[1])<=args.target:
                    cuts.update(tuple(map(int,tag.split(","))) for tag,row in read(qfile).get(k,{}).items() if row["status"]=="excluded")
            def visit(prefix):
                if tuple(prefix) in cuts:return
                if len(prefix)<=args.depth:
                    for v in legal(set(p),prefix):
                        if len(prefix)>1 or not args.first or v in args.first:visit(prefix+[v])
                    return
                tag=",".join(map(str,prefix));row=dest.get(tag,{})
                if row.get("status") in ("excluded","witness"):return
                n=args.target-98-len(prefix)
                ans=h.rebuild.solve(HERE,tmp,tools,mask(p,prefix),n,[0],row.get("cycles",[]),[],args.seconds)
                ans["encoding"]="parity-deficit"
                if ans["status"]=="witness":
                    b=prefix[:-1]+[u^prefix[-1] for u in ans["path"]];ans["witness"]=witness(p,b)
                    assert ans["witness"]["edges"]==args.target
                    if args.target>=192:save(HERE/"candidate-192.json",ans["witness"])
                dest[tag]=ans;save(f,out);print("Query",k[:8],args.target,prefix,ans["status"],flush=True)
            visit([0])

def audit(roots):
    h=hunt();audit=h.original_audit;audit.HERE=HERE;old=older(max((int(f.stem.split("-")[1]) for f in HERE.glob("queries-*.json")),default=187))
    placed=read(HERE/"placements.json") if (HERE/"placements.json").exists() else {}
    output={}
    for k,r in roots.items():
        p=r["parent"];w=placed.get(k,{}).get("best",witness(p,r["old"]["partner"]))
        assert witness(p,w["partner"])==w and audit.path_edges(w["joined"],9)==w["edges"]
        output[k]=dict(shape=r["shape"],parent=p,minimum=w["edges"],maximum=r["old"]["upper"],best=w,targets={})
    with TemporaryDirectory(prefix="q9-replay276-") as t:
        tmp=Path(t);checker=h.rebuild.masks.compilers(tmp)[0]
        for f in sorted(HERE.glob("queries-*.json")):
            target=int(f.stem.split("-")[1])
            for k,d in read(f).items():
                r=roots[k];p=r["parent"];cuts={pref for n,pref in old[k] if n<=target}
                direct=set();status=Counter()
                for addr,row in d.items():
                    q=list(map(int,addr.split(",")));assert audit.path_edges(q,8)==len(q)-1 and q[0]==0 and set(q)&set(p)=={0}
                    step=q[-1];oldtip=set(q[:-1]);bad=set(p[1:])
                    for v in oldtip:
                        bad.add(v);bad.update(v^(1<<j) for j in range(8))
                    bad.discard(step)
                    audit.replay([{v^step for v in bad}],target-98-len(q),row,tmp,checker)
                    status[row["status"]]+=1
                    if row["status"]=="witness":
                        b=q[:-1]+[v^step for v in row["path"]];w=witness(p,b)
                        assert w==row["witness"] and audit.path_edges(w["joined"],9)==target
                        if w["edges"]>output[k]["minimum"]:output[k].update(minimum=target,best=w)
                    elif row["status"]=="excluded":direct.add(tuple(q))
                covered=cuts|direct;todo=[];limit=max(map(len,covered),default=1)
                def compress(q):
                    if tuple(q) in covered:return
                    if len(q)>=limit:todo.append(q);return
                    for v in h.next_sites(q,set(p)):compress(q+[v])
                compress([0])
                if not todo:output[k]["maximum"]=min(output[k]["maximum"],target-1)
                output[k]["targets"][target]=dict(statuses=status,prior_prefixes=sorted(cuts),new_prefixes=sorted(direct),uncovered=todo)
    assert all(v["minimum"]<=v["maximum"] for v in output.values())
    save(HERE/"endpoint-results.json",output)
    for k,row in output.items():print("Bounds",k[:8],row["minimum"],row["maximum"],flush=True)

def main():
    ap=ArgumentParser();ap.add_argument("action",choices=("construct","search","audit"))
    ap.add_argument("--steps",type=int,default=2000);ap.add_argument("--passes",type=int,default=1)
    ap.add_argument("--roots",nargs="+");ap.add_argument("--target",type=int,default=187)
    ap.add_argument("--seconds",type=float,default=4);ap.add_argument("--depth",type=int,default=0)
    ap.add_argument("--first",nargs="+",type=int);a=ap.parse_args();roots=cases()
    if a.action=="construct":construct(roots,a.steps,a.passes)
    elif a.action=="search":search(roots,a)
    else:audit(roots)
if __name__=="__main__":main()
