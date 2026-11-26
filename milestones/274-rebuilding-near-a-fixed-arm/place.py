"""Place the available long eight-cube donor segments at each retained-arm crossing."""
from near import HERE,MS,read,write,shape,valid,ArgumentParser
from hashlib import sha256
from pathlib import Path
from tempfile import TemporaryDirectory
import subprocess,sys
sys.path.insert(0,str(MS/"270-optimal-seven-dimensional-arms"))
from place_historical import library,segments,physical,rename,bank,checked,CSC,label,identifier

def run(source,iterations,top):
    data=read(HERE/(source+"-paths.json"))
    pool=set(library())
    for f in HERE.glob("*-paths.json"):
        pool.update(bytes.fromhex(s) for s in read(f)["shapes"])
    pool.update(bytes.fromhex(shape(r["path"])) for r in read(MS/"246-eight-dimensional-parents/donors.json")["shapes"])
    history=read(MS/"270-optimal-seven-dimensional-arms/opposite-constructions.json")["roots"]
    for r in history.values():
        pool.add(bytes.fromhex(r["shape"]));pool.add(bytes.fromhex(shape(r["best"]["B"])))
    for r in read(MS/"271-rebuilt-historical-partners/long-joins.json")["witnesses"]:
        for p in (r["parent"],r["partner"]): pool.add(bytes.fromhex(shape(p)))
    paths272=read(MS/"272-forty-nine-edge-parents/q8-arms.json")
    pool.update(bytes.fromhex(k) for k in paths272)
    if (HERE/"selected-start.json").exists():
        for r in read(HERE/"selected-start.json").values():
            for p in (r["seed"],r["other"]):pool.add(bytes.fromhex(shape(p)))
    pool=sorted(pool)
    paths=[list(physical(w)) for w in pool]
    origins=segments(pool,84,98);words=sorted(origins)
    pool_digest=sha256(b"\n".join(w.hex().encode() for w in pool)).hexdigest()
    images=list(bank.permutation_images())
    cases={}
    for s,r in data["shapes"].items():
        for q in (r["path"],r["path"][::-1]):
            A=label(q)[0]
            cases.setdefault(identifier(A),dict(parent=A,shape=s))
    dest=HERE/(source+"-placements.json")
    out=read(dest) if dest.exists() else {}
    if out.get("pool_sha256")!=pool_digest:
        out=dict(donors=len(pool),words=len(words),pool_sha256=pool_digest,roots={})
    earlier={}
    for f in HERE.glob("*-placements.json"):
        if f!=dest:
            previous=read(f)
            if previous.get("pool_sha256")==pool_digest:
                earlier.update(previous["roots"])
    rows=out["roots"]
    for k,r in sorted(cases.items()):
        if k in rows:continue
        A=r["parent"]
        if k in earlier:
            old=earlier[k]
            assert old["parent"]==A and old["shape"]==r["shape"]
            w=old["best"];valid(w["joined"],9)
            rows[k]=dict(old)
            continue
        maps=bank.allowed_maps(A,images);fit=bank.longest(words,maps)
        selected=bank.make_witness(paths,origins[fit[1]],fit,A)
        B=selected["partner"];w=checked(A,B);valid(w["joined"],9)
        rows[k]=dict(**r,best=w,initial=w["edges"],donor_placement=selected)
        if w["edges"]>=192:write(HERE/"candidate-192.json",w)
        if len(rows)%32==0:write(dest,out)
    write(dest,out)
    with TemporaryDirectory() as f:
        exe=Path(f)/"Grow.exe"
        subprocess.run([str(CSC),"/nologo","/optimize+","/out:"+str(exe),str(MS/"265-joint-arm-regrowth/JoinedSearch.cs")],capture_output=True,check=True)
        for i,k in enumerate(sorted(rows,key=lambda k:(-rows[k]["initial"],k))[:top]):
            r=rows[k]
            if "regrowth" in r:continue
            A=r["parent"];start=r["best"]["B"];salt=274000+i
            run=subprocess.run([str(exe),str(salt),str(iterations),"fixed"],text=True,capture_output=True,check=True,input="".join(",".join(map(str,p))+"\n" for p in (A,start))).stdout.splitlines()
            first,other=[list(map(int,l.split(","))) for l in run[:2]]
            assert first==A and len(other)>=len(start)
            w=checked(first,other);valid(w["joined"],9);r["best"]=w
            r["regrowth"]=dict(iterations=iterations,seed=salt)
            if w["edges"]>=192:write(HERE/"candidate-192.json",w)
    out.update(best=max((r["best"]["edges"] for r in rows.values()),default=None),fixed_roots=len(rows))
    write(dest,out)
    print(source,out["fixed_roots"],out["best"],"best before regrowth",max((v["initial"] for v in rows.values()),default=None))
if __name__=="__main__":
    ap=ArgumentParser();ap.add_argument("--source",default="common92");ap.add_argument("--iterations",type=int,default=4500);ap.add_argument("--top",type=int,default=15);a=ap.parse_args()
    run(a.source,a.iterations,a.top)
