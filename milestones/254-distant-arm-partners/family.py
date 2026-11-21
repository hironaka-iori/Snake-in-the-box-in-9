"""Search opposite-face partners over all four parity-preserving parents at each crossing."""
from argparse import ArgumentParser
from itertools import combinations, product
import gzip
import json
from pathlib import Path
import subprocess
import sys
from tempfile import TemporaryDirectory
from time import monotonic

HERE=Path(__file__).resolve().parent
PRIOR=HERE.parent/"252-shorter-reference-segments"
sys.path.insert(0,str(PRIOR))
from partners import previous as solver
from partners251 import require,read,file_hash,path_ok

LEDGER=HERE/"family-caps.json"


def root_family(shapes,root):
    paths={}
    for key,p in shapes.items():
        if root not in (p[0],p[-1]):continue
        seq=p if p[0]==root else p[::-1]
        paths[key]=[v^root for v in seq]
    masks={k:frozenset(p[1:]) for k,p in paths.items()}
    common=frozenset.intersection(*masks.values())
    choices={frozenset(m-common) for m in masks.values()}
    optional=sorted(frozenset.union(*choices))
    # Missing pairs never occur together in a parent. Each is one independent choice.
    pairs=[(a,b) for a,b in combinations(optional,2) if frozenset((a,b)) not in choices]
    require(len(paths)==4 and len(common)==94 and len(pairs)==2 and len(set(sum((list(p) for p in pairs),[])))==4
            and {frozenset(v) for v in product(*pairs)}==choices,"Families are not a product of two choices")
    return paths,sorted(common),pairs


def formula(common,pairs,n,cycles):
    cnf,chosen=solver.model([0,*common],n,[])
    cnf.clauses.extend([-chosen[a],-chosen[b]] for a,b in pairs)
    cnf.clauses.extend(solver.check_cycle(c,chosen) for c in cycles)
    return cnf,chosen


def search(paths,common,pairs,n,seconds,tmp,checker,trimmer,saved,prefix):
    cycles=list(saved.get("cycles",[]))
    until=monotonic()+seconds
    instance=tmp/"input.cnf";raw=tmp/"full.lrat"
    while True:
        cnf,chosen=formula(common,pairs,n,cycles)
        cnf.clauses.extend([chosen[v]] for v in prefix[1:])
        key=cnf.save(instance)
        record=dict(length=n,prefix=prefix,cycles=cycles,cnf=key,variables=cnf.count,clauses=len(cnf.clauses))
        try:
            ans=subprocess.run([str(solver.joins.partner.SOLVER),"-q","--seed=1","--lrat","--no-binary",
                                str(instance),str(raw)],capture_output=True,timeout=max(.01,until-monotonic()))
        except subprocess.TimeoutExpired:return dict(status="open",**record)
        if ans.returncode==20 and b"s UNSATISFIABLE" in ans.stdout:
            full=tmp/"full.gz";tiny=tmp/"small.lrat";spool=tmp/"hints.bin"
            solver.joins.archive(raw,full);raw.unlink()
            subprocess.run([str(trimmer),str(len(cnf.clauses)),str(full),str(spool),str(tiny)],
                           check=True,capture_output=True,timeout=120)
            spool.unlink()
            path=HERE/"family-proofs"/(key+".lrat.gz");path.parent.mkdir(exist_ok=True)
            raw_hash=solver.joins.archive(tiny,path);tiny.unlink()
            receipt=solver.check_proof(instance,path,checker)
            return dict(status="excluded",**record,proof=path.relative_to(HERE).as_posix(),raw=raw_hash,
                        compressed=file_hash(path),replay=receipt)
        require(ans.returncode==10 and b"s SATISFIABLE" in ans.stdout,"Unexpected SAT result")
        true={int(v) for l in ans.stdout.splitlines() if l.startswith(b"v ") for v in l.split()[1:]}
        selected={v for v in chosen if chosen[v] in true}
        possible=[k for k,p in paths.items() if selected.intersection(p)=={0}]
        require(possible,"Selected vertices block every parent")
        found,extra=solver.joins.opposite.extract(paths[possible[0]],n,prefix,selected)
        if found:
            return dict(status="witness",**record,compatible_shapes=possible,**found)
        require(extra,"Disconnected model without a cycle")
        cycles.extend(extra)


def main():
    cli=ArgumentParser(description=__doc__)
    cli.add_argument("--roots",type=int,nargs="+",default=[161,67,193,1])
    cli.add_argument("--lengths",type=int,nargs="+",default=[95,94,92])
    cli.add_argument("--seconds",type=int,default=4)
    cli.add_argument("--total",type=int,default=100)
    cli.add_argument("--split",action="store_true",help="Exhaust the legal first steps after an open full query")
    cli.add_argument("--replay",action="store_true")
    args=cli.parse_args()
    src=HERE/"parity-families.json"
    shapes=read(src)["shapes"]
    files=[src,Path(__file__),Path(solver.__file__),Path(solver.joins.partner.__file__),
           Path(solver.joins.opposite.__file__),solver.joins.CHECKER,solver.joins.COMPILER,
           solver.joins.partner.SOLVER,PRIOR/"TrimLrat.cs",Path(solver.joins.__file__),
           solver.joins.LAST/"endpoint94.py",solver.PREV/"audit.py"]
    pins={p.name:file_hash(p) for p in files}
    results=read(LEDGER) if LEDGER.exists() else dict(pins=pins,roots={})
    require(results["pins"]==pins,"Input changed")
    with TemporaryDirectory(prefix="snake254-fam-") as name:
        tmp=Path(name);checker=tmp/"VerifyLrat.exe";trimmer=tmp/"TrimLrat.exe"
        for c,exe in ((solver.joins.CHECKER,checker),(PRIOR/"TrimLrat.cs",trimmer)):
            subprocess.run([str(solver.joins.COMPILER),"/nologo","/optimize+","/out:"+str(exe),str(c)],check=True)
        until=monotonic()+args.total
        summary={}
        for root in args.roots:
            paths,common,pairs=root_family(shapes,root)
            row=results["roots"].setdefault(str(root),dict(parents=sorted(paths),blocked=common,
                                            optional_pairs=[list(pair) for pair in pairs],attempts={}))
            require(row["parents"]==sorted(paths) and row["blocked"]==common and row["optional_pairs"]==
                    [list(pair) for pair in pairs],"Recorded family differs")
            steps=[1<<j for j in range(8) if (1<<j) not in common]
            lengths=sorted(map(int,row["attempts"])) if args.replay else args.lengths
            for n in lengths:
                require(1<=n<=95,"Unsupported length")
                items=row["attempts"].setdefault(str(n),{})
                prefixes=[0,*steps] if args.split else [0]
                if args.replay:prefixes=sorted(map(int,items))
                for step in prefixes:
                    idx=str(step);prev=items.get(idx,{})
                    require(step==0 or step in steps,"Unknown first step")
                    prefix=[0,step] if step else [0]
                    if args.replay:
                        require(prev["prefix"]==prefix and prev["length"]==n,"Prefix or length mismatch")
                        cnf,chosen=formula(common,pairs,n,prev["cycles"])
                        cnf.clauses.extend([chosen[v]] for v in prefix[1:]);source=tmp/"verify.cnf"
                        require(cnf.save(source)==prev["cnf"] and len(cnf.clauses)==prev["clauses"]
                                and cnf.count==prev["variables"],"Reconstructed instance differs")
                        if prev["status"]=="excluded":
                            f=HERE/prev["proof"]
                            require(file_hash(f)==prev["compressed"] and file_hash(f,gzip.open)==prev["raw"]
                                    and solver.check_proof(source,f,checker)==prev["replay"],"Refutation failed")
                        elif prev["status"]=="witness":
                            partner=prev["partner"]
                            require(len(partner)==n+1 and partner[:len(prefix)]==prefix,"Invalid witness")
                            compatible=[k for k,p in paths.items() if set(p)&set(partner)=={0}]
                            require(compatible==prev["compatible_shapes"],"Incorrect witnessed parents")
                            for k in compatible:path_ok(paths[k][::-1]+[v+256 for v in partner],9)
                    else:
                        if step and items.get("0",{}).get("status") in ("excluded","witness"):break
                        if prev.get("status") in ("excluded","witness"):continue
                        if monotonic()>=until:break
                        rec=search(paths,common,pairs,n,min(args.seconds,max(.01,until-monotonic())),tmp,
                                   checker,trimmer,prev,prefix)
                        items[idx]=rec;solver.joins.save_json(LEDGER,results)
                        print(root,n,prefix,rec["status"],flush=True)
            caps=[];best=0
            for target,items in row["attempts"].items():
                n=int(target)
                if items.get("0",{}).get("status")=="excluded" or all(
                        items.get(str(s),{}).get("status")=="excluded" for s in steps):caps.append(n-1)
                if any(v["status"]=="witness" for v in items.values()):best=max(best,n)
            upper=min([98,*caps]);require(best<=upper,"Contradictory bounds")
            summary[root]=dict(partner_upper=upper,solver_witness_lower=best,shapes=sorted(paths))
        if args.replay:
            solver.joins.save_json(HERE/"family-replay.json",dict(ledger=file_hash(LEDGER),roots=summary))
        print({k:(v["solver_witness_lower"],v["partner_upper"]) for k,v in summary.items()},flush=True)


if __name__=="__main__":main()
