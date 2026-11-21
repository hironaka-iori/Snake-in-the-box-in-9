"""Preview or publish shorter LRAT archives after rechecking them against the exact CNF."""
from argparse import ArgumentParser
import gzip
from pathlib import Path
import shutil
import subprocess
from tempfile import TemporaryDirectory
from time import monotonic

import partners as cases
from partners import HERE, previous, require, read, file_hash

SOURCE = HERE / "TrimLrat.cs"
HISTORY = HERE / "trim-history.json"
JOURNAL = HERE / "trim-transaction.json"
PENDING = HERE / "trim-pending.lrat.gz"
KEYS = ("raw", "compressed", "replay")


def inventory(pool):
    entries = {}
    for parent in pool["roots"].values():
        for t in (191, 192):
            for row in parent.get(str(t), []):
                if row["status"] != "excluded":
                    continue
                key = row["cnf"]
                require(row["proof"]=="proofs/"+key+".lrat.gz", "Unbound proof path")
                entries.setdefault(key, []).append((parent["parent"],t,row))
    return entries


def finish(pool, entries, history):
    """Finish a verified one-proof replacement if a previous invocation was interrupted."""
    tx = read(JOURNAL)
    key, old, new = tx["cnf"], tx["old"], tx["new"]
    live = HERE/"proofs"/(key+".lrat.gz")
    current = file_hash(live)
    if current != new["compressed"]:
        require(current==old["compressed"] and PENDING.exists()
                and file_hash(PENDING)==new["compressed"], "Pending certificate differs")
        PENDING.replace(live)
    for _, _, row in entries[key]:
        require(any(all(row[k]==before[k] for k in KEYS) for before in (old,new)),
                "Ledger entry changed during proof replacement")
        row.update({k:new[k] for k in KEYS})
    previous.joins.save_json(cases.POOL,pool)
    history["proofs"][key]=tx
    previous.joins.save_json(HISTORY,history)
    JOURNAL.unlink()


def run():
    cli = ArgumentParser(description=__doc__)
    cli.add_argument("--apply",action="store_true",help="replace verified archives and their receipts")
    cli.add_argument("--limit",type=int,default=1,help="maximum proofs in this invocation, largest first")
    cli.add_argument("--total",type=float,default=250,help="stop beginning new proofs after this many seconds")
    cli.add_argument("--cnf",help="select one unique CNF hash or initial characters")
    args=cli.parse_args()
    require(args.limit>0 and args.total>0,"Positive limits required")
    pins={p.name:file_hash(p) for p in (Path(__file__),SOURCE,previous.joins.CHECKER,previous.joins.COMPILER)}
    pool=read(cases.POOL)
    old, _, model_pins=cases.sources()
    require(pool["pins"]==model_pins,"Partner dependencies differ")
    entries=inventory(pool)
    history=read(HISTORY) if HISTORY.exists() else dict(pins=pins,proofs={})
    require(history["pins"]==pins,"Trimmer or checker changed")
    if JOURNAL.exists():
        require(args.apply,"Resume previous verified transaction with --apply")
        finish(pool,entries,history)
    selected=[k for k in entries if (not args.cnf or k.startswith(args.cnf))]
    if args.cnf: require(len(selected)==1,"Missing or ambiguous proof")
    selected=[k for k in selected if k not in history["proofs"]]
    def certificate(k):
        return HERE / entries[k][0][2]["proof"]
    selected.sort(key=lambda k:certificate(k).stat().st_size,reverse=True)
    save=previous.joins.save_json
    previews={}
    until=monotonic()+args.total
    with TemporaryDirectory(prefix="q9-trim252-") as scratch:
        folder=Path(scratch)
        checker, trimmer=folder/"VerifyLrat.exe",folder/"TrimLrat.exe"
        for src,exe in ((previous.joins.CHECKER,checker),(SOURCE,trimmer)):
            subprocess.run([str(previous.joins.COMPILER),"/nologo","/optimize+","/out:"+str(exe),str(src)],
                           check=True,timeout=60,capture_output=True)
        for key in selected[:args.limit]:
            if monotonic()>=until: break
            parent,t,row=entries[key][0]
            original={k:row[k] for k in KEYS}
            original["bytes"]=certificate(key).stat().st_size
            for _,_,r in entries[key]:
                require(all(r[k]==original[k] for k in KEYS),"Two receipts disagree for the same contradiction")
            cases.check_prefix(parent,t-len(parent),row)
            previous.validate_rules(parent,t-len(parent),row["rules"],old)
            cnf,chosen=cases.anchored_model(tuple(row["prefix"]))(parent,t-len(parent),row["rules"])
            cnf.clauses.extend(previous.check_cycle(c,chosen) for c in row["cycles"])
            input_file=folder/"verify.cnf"
            require((cnf.save(input_file),len(cnf.clauses),cnf.count)==(key,row["clauses"],row["variables"]),
                    "Formula reconstruction differs")
            require(file_hash(certificate(key))==original["compressed"]
                    and file_hash(certificate(key),gzip.open)==original["raw"],"Original archive changed")
            spool,raw=folder/"hints.bin",folder/"cone.lrat"
            subprocess.run([str(trimmer),str(row["clauses"]),str(certificate(key)),str(spool),str(raw)],
                           check=True,capture_output=True,timeout=120)
            spool.unlink()
            trimmed=folder/"cone.lrat.gz"
            raw_hash=previous.joins.archive(raw,trimmed)
            raw.unlink()
            replay=previous.check_proof(input_file,trimmed,checker)
            new=dict(raw=raw_hash,compressed=file_hash(trimmed),bytes=trimmed.stat().st_size,replay=replay)
            item=dict(cnf=key,old=original,new=new,improved=new["bytes"]<original["bytes"])
            previews[key]=item
            print(key[:12],original["bytes"],"->",new["bytes"],"verified",flush=True)
            if not args.apply:
                save(HERE/"trim-preview.json",dict(pins=pins,proofs=previews))
            elif not item["improved"]:
                history["proofs"][key]=item
                save(HISTORY,history)
            else:
                # The candidate and live archive now share a filesystem. Keep the
                # publication journal until both the ledger and receipt are saved.
                shutil.copyfile(trimmed,PENDING)
                require(file_hash(PENDING)==new["compressed"],"Staging copy differs")
                save(JOURNAL,item)
                finish(pool,entries,history)


if __name__=="__main__":
    run()
