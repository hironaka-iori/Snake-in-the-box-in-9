"""Encode compatibility with at least one parent by the minimal sets hitting all parents."""
from collections import defaultdict
from pathlib import Path
from tempfile import TemporaryDirectory
import sys

HERE=Path(__file__).resolve().parent
MS=HERE.parent
sys.path.insert(0,str(MS/"262-common-forbidden-sites"))
import masks
from masks import load,save,digest,bank,p,groups,compilers,query,replay
sys.path.insert(0,str(MS/"260-donor-intersections"))
from replay import columns

def bits(vertices): return sum(1<<v for v in vertices)
def sites(mask): return [v for v in range(mask.bit_length()) if mask>>v & 1]

def minimal(items):
    keep=[]
    for m in sorted(set(items),key=lambda x:(x.bit_count(),x)):
        if not any(a&m==a for a in keep): keep.append(m)
    return keep

def transversals(extras):
    hits=[0]
    for row in extras:
        need=bits(row)
        opts=[1<<u for u in row]
        hits=minimal(x for t in hits for x in ([t] if t&need else [t|bit for bit in opts]))
    return [sites(t) for t in hits]

def sources():
    old={}
    files=[]
    for name,ledger in [("255-parity-exchange-arms/shared-proofs","cases.json"),
                        ("257-three-exchange-parents","partner-caps.json"),
                        ("258-four-exchange-parents","partner-caps.json"),("259-four-exchange-component","partner-caps.json")]:
        folder=MS/name
        rec=folder/"partner-replay-95.json"
        ledger=folder/ledger
        r=load(rec)
        if r["ledger_sha256"]!=digest(ledger): raise ValueError("Stale rooted archive")
        stored=load(ledger)["roots"]
        for row in r["roots"]:
            if row["status"]!="excluded": continue
            key=row["shape"]+":"+str(row["end"])
            old[name+"/"+key]=set(stored[key]["parent"][1:])
        files.extend([rec,ledger])
    agg=MS/"254-distant-arm-partners/aggregate.json"
    for r in load(agg)["cases"]:
        if r["partner_upper"]<95: old["254/"+r["shape"]+":"+str(r["root"])]=set(r["parent"][1:])
    files.append(agg)
    # Archive covers both orientations and records the actual labelled representative.
    focus=MS/"255-parity-exchange-arms/focus-closure.json"
    f=load(focus)
    for k,history in f["rooted_status_through_254"].items():
        for r in history:
            if r["target_192"]=="excluded":
                seq=f["paths"][k]
                root=(seq[0],seq[-1])[r["end"]]
                if root!=r["root"]: raise ValueError("Root label mismatch")
                old["focus/"+k+":"+str(root)]={x^root for x in seq if x!=root}
    files.append(focus)
    core=MS/"262-common-forbidden-sites/groups.json"
    for tag,r in load(core).items():
        if r["status"]=="excluded": old["262/"+tag]=set(r["blocked"])
    return old,files+[core]

def inherited(blocked,old,images):
    # Tabulate *every* axis permutation moving at most twelve source blockers beyond this group.
    inside=bank.allowed_maps([0]+sorted(set(range(1,256))-blocked),images)
    candidates={}
    for key,S in sorted(old.items()):
        counts=columns((bank.ALL_MAPS^inside[v]) for v in S)
        equal=bank.ALL_MAPS
        less=0
        for j in reversed(range(len(counts))):
            if (12>>j)&1:
                less|=equal&~counts[j]
                equal&=counts[j]
            else: equal&=~counts[j]
        live=less|equal
        while live:
            bit=live&-live
            rank=bit.bit_length()-1
            freed={images[rank][v] for v in S}-blocked
            if len(freed)>12: raise ValueError("Intersection count differs")
            candidates.setdefault(bits(freed),dict(source=key,rank=rank,sites=sorted(freed)))
            live^=bit
    return [candidates[m] for m in minimal(candidates)]

def setup(tags,targets,old,images):
    blocked=set.intersection(*(targets[k] for k in tags))
    extra=[sorted(targets[k]-blocked) for k in tags]
    negative=transversals(extra)
    positive=inherited(blocked,old,images)
    for rule in positive:
        if set(rule["sites"])!={images[rule["rank"]][v] for v in old[rule["source"]]}-blocked:
            raise ValueError("Invalid transported exclusion")
    def build(forbidden,cycles,alternatives,prefix):
        if forbidden!=blocked or alternatives!=extra: raise ValueError("Family input differs")
        cnf,chosen=masks.formula(blocked,cycles,prefix=prefix)
        for t in negative: cnf.clauses.append([-chosen[v] for v in t])
        for rule in positive: cnf.clauses.append([chosen[v] for v in rule["sites"]])
        return cnf,chosen
    return blocked,extra,negative,positive,build

def run():
    from argparse import ArgumentParser
    parser=ArgumentParser()
    parser.add_argument("seconds",type=float)
    parser.add_argument("--root",type=int,nargs="+")
    parser.add_argument("--shape",nargs="+",help="Restrict a physical root to the matching parent shapes")
    parser.add_argument("--split",type=int,default=0,help="Search a prefix of the specified depth")
    parser.add_argument("--replay",action="store_true")
    args=parser.parse_args()
    dest=HERE/"decisions.json"
    data=load(dest) if dest.exists() else {}
    old,files=sources()
    images=list(bank.permutation_images())
    areas=groups()
    with TemporaryDirectory() as td:
        tmp=Path(td)
        tools=compilers(tmp)
        for root in (args.root or sorted(areas)):
            targets=areas[root]
            tags=sorted(targets)
            if args.shape:
                tags=[t for t in tags if any(t.startswith(s) for s in args.shape)]
                if not tags: continue
            label=str(root) if set(tags)==set(targets) else str(root)+"."+".".join(t[:12] for t in tags)
            blocked,extra,negative,positive,build=setup(tags,targets,old,images)
            desc=dict(members=tags,blocked=sorted(blocked),extra=extra,negative=negative,positive=positive,
                      source_pins={f.relative_to(MS).as_posix():digest(f) for f in files})
            entry=data.setdefault(label,dict(description=desc,queries={}))
            if entry["description"]!=desc: raise ValueError("Geometry or cuts changed")
            records=entry["queries"]
            if any(not r["sites"] for r in positive):
                # The whole forbidden mask contains a transported certified obstruction.
                entry["inherited"]=True
                if not args.replay: save(dest,data)
                continue
            def visit(prefix):
                key=",".join(map(str,prefix))
                row=records.get(key)
                if not args.replay and len(prefix)-1==args.split and (row is None or row["status"]=="open"):
                    row=query(HERE,tmp,tools,blocked,args.seconds,extra,prefix,row,builder=build)
                    records[key]=row
                    save(dest,data)
                    print(root,key,"cuts",len(negative),len(positive),row["status"],flush=True)
                if row and row["status"] in ("excluded","witness"): return
                if len(prefix)-1<args.split:
                    for v in p.joins.partner.next_vertices([0]+sorted(blocked),prefix): visit(prefix+[v])
            if args.replay:
                for q in records.values(): replay(HERE,tmp,tools[0],q,builder=build)
            else: visit([0])
    if args.replay: print("Replayed",sum(len(r["queries"]) for r in data.values()),"recorded prefixes")

if __name__=="__main__": run()
