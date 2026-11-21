"""Reinforce the four-parent choice formula by earlier rooted upper bounds."""
from argparse import ArgumentParser
import gzip
from pathlib import Path
from tempfile import TemporaryDirectory
from time import monotonic
import subprocess
import family as base
import fixed
from family import solver, read, require, file_hash, path_ok

HERE=Path(__file__).resolve().parent
LEDGER=HERE/"cut-caps.json"


def sources():
    old,pins,cases=fixed.sources()
    for name in ("sat-caps.json","sibling-caps.json"):
        ledger=read(HERE/name)
        pins[name]=file_hash(HERE/name)
        for tag,row in ledger["roots"].items():
            parent=cases[tag][2]
            require(row["parent"]==parent,"Different orientation for an inherited query")
            caps=[a["length"]-1 for a in row["attempts"] if a["status"]=="excluded"]
            if caps:old[name+"/"+tag,0]=(parent,min(caps))
    for p in (Path(__file__),HERE/"family.py",HERE/"parity-families.json",HERE/"sibling.py"):
        pins[p.name]=file_hash(p)
    return old,pins


def get_rules(paths,common,old,index):
    # Ordered 16-step matches supply useful isometries. Every suggested cut is
    # checked by reconstructing the whole old rooted parent under that map.
    candidates={(key,tuple(range(8))) for key in old}
    for p in paths.values():
        for signature,order in solver.windows(p,5):
            for key,before in index.get(signature,()):
                candidates.add((key,tuple(order[before.index(i)] for i in range(8))))
    covered={0,*common};out={}
    for key,axes in sorted(candidates):
        path,cap=old[key]
        table=solver.images(axes)
        free=tuple(sorted({table[v] for v in path}-covered))
        if len(free)<=10 and (free not in out or cap<out[free]["cap"]):
            out[free]=dict(source=list(key),axes=list(axes),sites=list(free),cap=cap)
    return sorted(out.values(),key=lambda r:(len(r["sites"]),r["cap"],r["sites"]))


def main():
    cli=ArgumentParser(description=__doc__)
    cli.add_argument("--roots",type=int,nargs="+",default=[161,193,1,67])
    cli.add_argument("--lengths",type=int,nargs="+",default=[95])
    cli.add_argument("--seconds",type=int,default=5)
    cli.add_argument("--total",type=int,default=130)
    cli.add_argument("--split",action="store_true")
    cli.add_argument("--replay",action="store_true")
    args=cli.parse_args()
    old,pins=sources();index=solver.placement_index(old)
    original=read(HERE/"parity-families.json")["shapes"]
    d=read(LEDGER) if LEDGER.exists() else dict(pins=pins,roots={})
    require(pins==d["pins"],"Changed cut dependencies")
    with TemporaryDirectory(prefix="snake254-cut-") as name:
        tmp=Path(name);checker=tmp/"VerifyLrat.exe";trimmer=tmp/"TrimLrat.exe"
        for src,exe in ((solver.joins.CHECKER,checker),(base.PRIOR/"TrimLrat.cs",trimmer)):
            subprocess.run([str(solver.joins.COMPILER),"/nologo","/optimize+","/out:"+str(exe),str(src)],check=True)
        until=monotonic()+args.total
        summary={}
        for root in args.roots:
            paths,common,pairs=base.root_family(original,root)
            candidates=get_rules(paths,common,old,index)
            results=d["roots"].setdefault(str(root),{})
            steps=[1<<i for i in range(8) if (1<<i) not in common]
            for n in (sorted(map(int,results)) if args.replay else args.lengths):
                rules=solver.active_cuts(candidates,n)
                solver.validate_rules([0,*common],n,rules,old)
                def formula(blocked,options,length,cycles):
                    require((blocked,options,length)==(common,pairs,n),"Unexpected cut context")
                    cnf,chosen=solver.model([0,*common],n,rules)
                    cnf.clauses.extend([-chosen[a],-chosen[b]] for a,b in pairs)
                    cnf.clauses.extend(solver.check_cycle(c,chosen) for c in cycles)
                    return cnf,chosen
                result=results.setdefault(str(n),dict(rules=rules,cases={}))
                require(rules==result["rules"],"Regenerated cuts differ")
                cases=result["cases"]
                queries=sorted(map(int,cases)) if args.replay else [0,*(steps if args.split else [])]
                for step in queries:
                    prefix=[0,step] if step else [0]
                    prev=cases.get(str(step),{})
                    if args.replay:
                        require(prev["prefix"]==prefix and prev["length"]==n and (not step or step in steps),
                                "Invalid case")
                        cnf,chosen=formula(common,pairs,n,prev["cycles"])
                        cnf.clauses.extend([chosen[v]] for v in prefix[1:])
                        f=tmp/"verify.cnf"
                        require(cnf.save(f)==prev["cnf"] and cnf.count==prev["variables"] and
                                len(cnf.clauses)==prev["clauses"],"Invalid CNF")
                        if prev["status"]=="excluded":
                            proof=HERE/prev["proof"]
                            require(file_hash(proof)==prev["compressed"] and file_hash(proof,gzip.open)==prev["raw"]
                                    and solver.check_proof(f,proof,checker)==prev["replay"],"Verification failed")
                        elif prev["status"]=="witness":
                            p=prev["partner"];path_ok(p,8)
                            good=[k for k,v in paths.items() if set(p)&set(v)=={0}]
                            require(good and good==prev["compatible_shapes"] and len(p)==n+1 and p[:len(prefix)]==prefix,
                                    "Invalid positive record")
                            for k in good:path_ok(paths[k][::-1]+[v+256 for v in p],9)
                    else:
                        if step and cases.get("0",{}).get("status") in ("excluded","witness"):break
                        if prev.get("status") in ("excluded","witness"):continue
                        if monotonic()>=until:break
                        # Reuse the proof-producing search and its archive format. Only
                        # the formula builder changes; every extra clause is regenerated on replay.
                        base.formula=formula
                        row=base.search(paths,common,pairs,n,min(args.seconds,max(.01,until-monotonic())),tmp,
                                        checker,trimmer,prev,prefix)
                        cases[str(step)]=row;solver.joins.save_json(LEDGER,d)
                        print(root,n,prefix,len(rules),row["status"],flush=True)
            caps=[];seen=0
            for t,res in results.items():
                cases=res["cases"];n=int(t)
                if cases.get("0",{}).get("status")=="excluded" or all(cases.get(str(j),{}).get("status")=="excluded" for j in steps):caps.append(n-1)
                if any(v["status"]=="witness" for v in cases.values()):seen=max(seen,n)
            upper=min([98,*caps]);require(seen<=upper,"Conflicting evidence")
            summary[root]=dict(partner_upper=upper,solver_witness_lower=seen)
        if args.replay:solver.joins.save_json(HERE/"cut-replay.json",dict(roots=summary,ledger=file_hash(LEDGER)))
        print(summary,flush=True)


if __name__=="__main__":main()
