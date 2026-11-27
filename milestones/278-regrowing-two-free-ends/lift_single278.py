"""Place and reconstruct a single opposite Q8 arm at each endpoint of the three R277 donors."""
from argparse import ArgumentParser
from collections import defaultdict
from hashlib import sha256
from pathlib import Path
from tempfile import TemporaryDirectory
import subprocess
import sys

HERE=Path(__file__).resolve().parent
MS=HERE.parent
R277=MS/"277-shorter-seven-dimensional-arms"
R274=MS/"274-rebuilding-near-a-fixed-arm"
FOLDER=HERE/"one-crossing"
SOURCE=R277/"q8-new.json"
DIGEST="d36e3bc59b450e62cbf15c25b16213271f89f349ae3760d5da45b06e6b213b25"
sys.path.insert(0,str(R274))
import face274 as face
from face274 import read,save
sys.path.insert(0,str(MS/"270-optimal-seven-dimensional-arms"))
from place_historical import bank,word,checked,physical,segments,CSC

def plan():
    assert sha256(SOURCE.read_bytes()).hexdigest()==DIGEST
    roots={};ends={};families=defaultdict(list)
    for shape,obj in sorted(read(SOURCE).items()):
        p=obj["joined_q8"]
        assert len(p)==97 and word(p).hex()==shape
        bank.check_path(p,8)
        ends[shape]=[]
        for direction,q in enumerate((p,p[::-1])):
            k,normal,_=face.rooted(q);port=q[0];translated=[x^port for x in q]
            assert k not in roots
            roots[k]=dict(parent=translated,normalized=normal,raw_endpoint=port,minimum_omissions=0,
                          shape=shape,direction=direction)
            ends[shape].append(dict(root=k,raw_endpoint=port,direction=direction))
            families[port].append(k)
    assert len(roots)==6 and len(ends)==3
    groups=[dict(id="port-"+str(port),rank=0,raw_endpoint=port,parent_edges=96,minimum_omissions=0,keys=sorted(keys))
            for port,keys in sorted(families.items())]
    FOLDER.mkdir(exist_ok=True)
    ret=dict(roots=roots,endpoints=ends,groups=groups,input_sha256=DIGEST)
    save(FOLDER/"plan.json",ret)
    return ret

def donor_pool():
    sys.path.insert(0,str(R277))
    from summarize import old_pool
    refs=old_pool()
    donors={bytes.fromhex(k) for row in refs.values() for k in row["words"]}
    from construct import donor_words
    earlier,_=donor_words(set());donors.update(earlier)
    extra={}
    def add(key,rows):
        values={word(p) for p in rows}
        extra[key]=len(values);donors.update(values)
    for name in ("q8-arms.json","shorter-witnesses.json","nearby-shortened-single-parents.json"):
        p=R277/name
        add(name,[r["joined_q8"] for r in read(p).values()])
    previous=read(R274/"union-placements.json")["roots"]
    add("R274 placement partners",[r["best"]["B"] for r in previous.values()])
    selected=read(R274/"selected-start.json")
    add("R274 starting arms",[p for row in selected.values() for p in (row["seed"],row["other"])])
    last=MS/"276-partners-of-optimal-arms"
    add("R276 partners",[r["best"]["partner"] for r in read(last/"endpoint-results.json").values()])
    return sorted(donors),extra

def reverse_count(words,maps,length):
    pats={w[:length] for w in words if len(w)>=length}
    n=0
    for w in pats:
        live=bank.ALL_MAPS
        for v in physical(w)[:0:-1]:
            live&=maps[v]
            if not live:break
        n+=live.bit_count()
    return len(pats),n

def place(data,iterations):
    sys.path.insert(0,str(MS/"273-partners-of-rebuilt-arms"))
    pool,extra=donor_pool()
    pool_hash=sha256(b"\n".join(w.hex().encode() for w in pool)).hexdigest()
    paths=[list(physical(w)) for w in pool];images=list(bank.permutation_images())
    origins=segments(pool,84,98);words=sorted(origins);lowest=84
    rows={}
    for k,r in data["roots"].items():
        p=r["normalized"];maps=bank.allowed_maps(p,images)
        fit=bank.longest(words,maps)
        # If the longest matched prefix is shorter than 83, unrepresented short
        # suffixes might win. Decrease the minimum until all longer suffixes occur.
        if fit[0]<lowest-1:
            lowest=max(1,fit[0]+1);origins=segments(pool,lowest,98);words=sorted(origins)
            fit=bank.longest(words,maps)
        assert fit[0]>=lowest-1
        q=bank.make_witness(paths,origins[fit[1]],fit,p)
        nwords,hits=reverse_count(words,maps,95)
        assert bool(hits)==(fit[0]>=95)
        nnext,successors=reverse_count(words,maps,fit[0]+1)
        assert successors==0
        best=checked(p,q["partner"])
        rows[k]=dict(shape=r["shape"],direction=r["direction"],parent=p,raw_endpoint=r["raw_endpoint"],
                     donor_word=pool[q["donor_index"]].hex(),placement=q,best=best,represented_minimum=lowest,
                     target95_words=nwords,target95_hits=hits,next_words=nnext,next_length=fit[0]+1,next_hits=successors)
        if best["edges"]>=192:save(FOLDER/"candidate-192-placement.json",best)
        print("Placed",k[:10],"at",best["edges"],"target hits",hits,flush=True)
    if iterations:
        with TemporaryDirectory(prefix="snake278-graft-") as td:
            exe=Path(td)/"Grow.exe"
            subprocess.run([str(CSC),"/nologo","/optimize+","/out:"+str(exe),str(MS/"265-joint-arm-regrowth/JoinedSearch.cs")],capture_output=True,check=True)
            for i,(k,r) in enumerate(rows.items()):
                a=r["parent"];b=r["best"]["B"];seed=278960+i
                proc=subprocess.run([str(exe),str(seed),str(iterations),"fixed"],input="".join(",".join(map(str,s))+"\n" for s in (a,b)),text=True,capture_output=True,check=True)
                p,q=[list(map(int,s.split(","))) for s in proc.stdout.splitlines()[:2]]
                assert a==p and len(q)>=len(b)
                r["regrowth"]=dict(seed=seed,iterations=iterations,before=r["best"]["edges"])
                r["best"]=checked(p,q)
                if r["best"]["edges"]>=192:save(FOLDER/"candidate-192-regrowth.json",r["best"])
    save(FOLDER/"single-placements.json",dict(roots=rows,source_sha256=DIGEST,pool_sha256=pool_hash,
         donor_shapes=len(pool),extra_sources=extra,permutations=len(images),target_words=rows[next(iter(rows))]["target95_words"],
         total_target_hits=sum(r["target95_hits"] for r in rows.values()),best=max(r["best"]["edges"] for r in rows.values())))
    print("Six-port best",max(r["best"]["edges"] for r in rows.values()),flush=True)

def main():
    cli=ArgumentParser();cli.add_argument("action",choices=["place","search","audit"])
    cli.add_argument("--iterations",type=int,default=2400);cli.add_argument("--target",type=int,default=192)
    cli.add_argument("--seconds",type=float,default=6);cli.add_argument("--depth",type=int,default=0)
    cli.add_argument("--only",type=int,nargs="+")
    opt=cli.parse_args();data=plan()
    if opt.action=="place":place(data,opt.iterations);return
    h=face.dependencies(MS)
    if opt.action=="search":
        opt.standard=False;opt.refined_only=False;opt.through=0;opt.parents=None
        face.search(FOLDER,data,opt,h,{})
        cand=FOLDER/("candidate-"+str(opt.target)+".json")
        if opt.target>=192 and cand.exists():
            rows=read(cand)
            for q in rows.values():assert bank.check_path(q,9) and len(q)-1==opt.target
            save(HERE/("candidate-"+str(opt.target)+"-one-crossing.json"),rows)
    else:
        face.audit(FOLDER,data,FOLDER,"single",h,dict(roots={}))
        result=read(FOLDER/"summary.json");print("Endpoint bounds",[(k[:8],r["minimum"],r["maximum"]) for k,r in result["roots"].items()])

if __name__=="__main__":main()
