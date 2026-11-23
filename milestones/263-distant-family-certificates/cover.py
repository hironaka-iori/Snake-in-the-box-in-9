"""Group remaining roots by shared blocked sites and refine inconclusive groups."""
from argparse import ArgumentParser
from pathlib import Path
from tempfile import TemporaryDirectory
from family import HERE,MS,groups,sources,setup,compilers,query,load,save,digest,bank

def complete(tag,root,F,data,prior):
    if tag in prior: return True
    known=set()
    for entry in data.values():
        if tag not in entry["description"]["members"]: continue
        if entry.get("inherited"): return True
        for q in entry["queries"].values():
            if q["status"]=="excluded": known.add(tuple(q["prefix"]))
    return (0,) in known or all((0,1<<i) in known for i in range(8) if (1<<i) not in F)

def cluster(tags,targets):
    parts=[(t,) for t in sorted(tags)]
    while len(parts)>1:
        choices=[]
        for a,g in enumerate(parts):
            for j in range(a+1,len(parts)):
                h=parts[j]
                if len(g+h)>4: continue
                common=set.intersection(*(targets[k] for k in g+h))
                if len(common)>=93: choices.append((-len(common),-(len(g)+len(h)),g,h))
        if not choices: break
        _,_,g,h=min(choices)
        parts.remove(g)
        parts.remove(h)
        parts.append(tuple(sorted(g+h)))
    return sorted(parts)

if __name__=="__main__":
    args=ArgumentParser()
    args.add_argument("seconds",type=float)
    args.add_argument("--root",type=int,nargs="+",default=[193,1,220,161,67])
    args.add_argument("--singles",action="store_true")
    args.add_argument("--split",action="store_true")
    cfg=args.parse_args()
    dest=HERE/"decisions.json"
    data=load(dest)
    pool=groups()
    old,files=sources()
    images=list(bank.permutation_images())
    prior={r["shape"]+":"+str(r["end"]) for r in load(MS/"257-three-exchange-parents/partner-replay-95.json")["roots"]
           if r["status"]=="excluded"} | set(load(MS/"262-common-forbidden-sites/transfer.json")["covered"])
    with TemporaryDirectory() as d:
        tmp=Path(d)
        tools=compilers(tmp)
        for root in cfg.root:
            family=pool[root]
            remaining=[t for t,F in family.items() if not complete(t,root,F,data,prior)]
            parts=[(t,) for t in sorted(remaining)] if cfg.singles else cluster(remaining,family)
            for group in parts:
                tags=sorted(group)
                label=str(root) if set(tags)==set(family) else str(root)+"."+".".join(t[:12] for t in tags)
                blocked,extra,negative,positive,build=setup(tags,family,old,images)
                desc=dict(members=tags,blocked=sorted(blocked),extra=extra,negative=negative,positive=positive,
                          source_pins={f.relative_to(MS).as_posix():digest(f) for f in files})
                entry=data.setdefault(label,dict(description=desc,queries={}))
                if entry["description"]!=desc: raise ValueError("Changed family")
                if any(not r["sites"] for r in positive):
                    entry["inherited"]=True
                    save(dest,data)
                    continue
                prefixes=[[0]] if not cfg.split else [[0,1<<j] for j in range(8) if (1<<j) not in blocked]
                for pre in prefixes:
                    key=",".join(map(str,pre))
                    existing=entry["queries"].get(key)
                    if existing and existing["status"]!="open": continue
                    r=query(HERE,tmp,tools,blocked,cfg.seconds,extra,pre,existing,builder=build)
                    entry["queries"][key]=r
                    save(dest,data)
                    print(root,len(tags),label,key,r["status"],flush=True)
                    if r["status"]=="witness": raise SystemExit("Inspect the 95-edge partner immediately")
