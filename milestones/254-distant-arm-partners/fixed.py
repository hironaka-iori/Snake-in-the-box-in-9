"""Solve unrestricted partner lengths for the four named rooted parents; replay saved proofs."""
from argparse import ArgumentParser
import gzip
from pathlib import Path
import subprocess
import sys
from tempfile import TemporaryDirectory
from time import monotonic

HERE=Path(__file__).resolve().parent
R253=HERE.parent/"253-repeated-segment-growth"
R252=HERE.parent/"252-shorter-reference-segments"
sys.path.insert(0,str(R252))
import partners as shared
from partners import previous as p, file_hash, read, require, rooted

p.HERE=HERE
POOL=HERE/"sat-caps.json"


def sources():
    old,_,pins=shared.sources()
    data=read(R252/"rooted-proofs.json")
    for key,r in data["roots"].items():
        parent=r["parent"]
        caps=[]
        for target in (191,192):
            if shared.covers((0,),shared.query_rows(r,target),parent,target-len(parent)):
                caps.append(target-len(parent)-1)
        if caps: old["252/"+key,0]=(parent,min(caps))
    paths=read(R253/"closure.json")["paths"]; baselines=read(R253/"remote-arms.json")["cases"]
    inputs=(Path(__file__),R253/"closure.json",R253/"remote-arms.json",R252/"rooted-proofs.json",
            R252/"TrimLrat.cs",R252/"replay-68-192.json")
    pins.update({q.name:file_hash(q) for q in inputs})
    cases={}
    for label in ("6f8ef24c","bac52b55"):
        matches=[(k,v) for k,v in paths.items() if k.startswith(label)]
        require(len(matches)==1,"Missing or ambiguous shape")
        key,seq=matches[0]; p.path_ok(seq,8)
        for end in (1,0):
            root=seq[-1] if end else seq[0]; parent=rooted(seq,end)
            w=next(r for r in baselines if r["id"]==key and r["end"]==end)
            require(w["root"]==root and len(parent)==97,"Incorrect parent or crossing")
            p.verified_partner(parent,w,w["partner_edges"])
            cases[f"{label}-{root}"]=(key,end,parent,w)
    return old,pins,cases


def compact(folder,checker,trimmer,row):
    if row["status"]!="excluded": return
    proof=HERE/row["proof"]
    cnf=folder/"partner.cnf"
    require(file_hash(cnf)==row["cnf"],"Original formula differs")
    spool,raw,archive=folder/"hints.bin",folder/"cone.lrat",folder/"cone.lrat.gz"
    subprocess.run([str(trimmer),str(row["clauses"]),str(proof),str(spool),str(raw)],
                   check=True,capture_output=True,timeout=120)
    spool.unlink()
    original_size=proof.stat().st_size
    raw_hash=p.joins.archive(raw,archive)
    raw.unlink()
    if archive.stat().st_size<original_size:
        receipt=p.check_proof(cnf,archive,checker)
        row["before_trim"]={k:row[k] for k in ("raw","compressed","replay")}
        row["before_trim"]["bytes"]=original_size
        row.update(raw=raw_hash,compressed=file_hash(archive),replay=receipt)
        import shutil
        tmp=proof.with_suffix(".pending"); shutil.copyfile(archive,tmp); tmp.replace(proof)
    row["bytes"]=proof.stat().st_size


def bounds(r):
    lo=r["prior_witness"]["partner_edges"];hi=98
    for item in r["attempts"]:
        if item["status"]=="witness":lo=max(lo,item["length"])
        if item["status"] in ("inherited","excluded"):hi=min(hi,item["length"]-1)
    require(lo<=hi,"Contradictory rooted capacity")
    return lo,hi


def main():
    cli=ArgumentParser(description=__doc__)
    cli.add_argument("--lengths",type=int,nargs="+",default=[95,94,93])
    cli.add_argument("--case",nargs="+")
    cli.add_argument("--seconds",type=float,default=5)
    cli.add_argument("--total",type=float,default=90)
    cli.add_argument("--retry",action="store_true")
    cli.add_argument("--replay",action="store_true")
    args=cli.parse_args()
    require(all(1<=n<=95 for n in args.lengths) and min(args.seconds,args.total)>0,"Bad search settings")
    old,pins,cases=sources()
    result=read(POOL) if POOL.exists() else dict(pins=pins,roots={})
    require(result["pins"]==pins,"Sources or dependencies differ")
    selected=args.case or list(cases)
    require(set(selected)<=set(cases),"Unknown rooted case")
    for tag,(key,end,parent,w) in cases.items():
        r=result["roots"].setdefault(tag,dict(id=key,end=end,root=w["root"],parent=parent,prior_witness=w,attempts=[]))
        require(r["parent"]==parent and r["id"]==key and r["end"]==end and r["prior_witness"]==w,"Root mismatch")
    index={} if args.replay else p.placement_index(old)
    with TemporaryDirectory(prefix="q9-fixed254-") as tmp:
        folder=Path(tmp); checker=folder/"VerifyLrat.exe"; trimmer=folder/"TrimLrat.exe"
        for src,exe in ((p.joins.CHECKER,checker),(R252/"TrimLrat.cs",trimmer)):
            subprocess.run([str(p.joins.COMPILER),"/nologo","/optimize+","/out:"+str(exe),str(src)],
                           check=True,capture_output=True,timeout=45)
        deadline=monotonic()+args.total
        candidates={}
        if args.replay:
            for tag in selected:
                r=result["roots"][tag]; parent=r["parent"]
                require(len(r["attempts"])==len({a["length"] for a in r["attempts"]}),"Duplicate target")
                for a in r["attempts"]:p.replay(parent,a["length"],a,old,folder,checker)
                lo,hi=bounds(r)
                require((lo,hi)==(r["lower"],r["upper"]),"Reported bounds differ")
            p.joins.save_json(HERE/"sat-replay.json",dict(pins=pins,ledger_sha256=file_hash(POOL),
                       roots=[dict(tag=t,lower=bounds(result["roots"][t])[0],upper=bounds(result["roots"][t])[1])
                              for t in selected]))
            return
        for n in args.lengths:
            for tag in selected:
                if monotonic()>=deadline:return
                r=result["roots"][tag];parent=r["parent"]
                lo,hi=bounds(r);prior=next((a for a in r["attempts"] if a["length"]==n),None)
                if not lo<n<=hi or (prior and (prior["status"]!="open" or not args.retry)):continue
                if tag not in candidates:candidates[tag]=p.transfers(parent,old,index)
                rules=p.active_cuts(candidates[tag],n)
                item=p.solve(parent,n,rules,old,folder,checker,min(args.seconds,max(.01,deadline-monotonic())),prior)
                compact(folder,checker,trimmer,item)
                item["length"]=n
                if prior:r["attempts"].remove(prior)
                r["attempts"].append(item)
                for rec in result["roots"].values():rec["lower"],rec["upper"]=bounds(rec)
                p.joins.save_json(POOL,result)
                print(tag,n,item["status"],"bounds",bounds(r),flush=True)


if __name__=="__main__":
    main()
