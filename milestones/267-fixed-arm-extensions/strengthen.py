"""Use earlier rooted exclusions and short sets of mutually conflicting optional sites."""
from argparse import ArgumentParser
from itertools import combinations
from pathlib import Path
from tempfile import TemporaryDirectory
from families import HERE,read,write,bank,masks,grouped_inputs,classify

def exclusions(extras):
    rows=list(map(set,extras))
    if any(not row for row in rows):return []
    optional=sorted(set.union(*rows))
    keep=[]
    for n in (2,3):
        for c in combinations(optional,n):
            s=set(c)
            if all(row&s for row in rows) and not any(set(h)<=s for h in keep):
                keep.append(c)
    return keep

def builder(cuts,negative):
    def build(blocked,cycles,extras,prefix):
        cnf,chosen=masks.formula(blocked,cycles,extras,prefix)
        for cut in cuts:
            cnf.clauses.append([chosen[v] for v in cut["sites"]])
        for sites in negative:
            cnf.clauses.append([-chosen[v] for v in sites])
        return cnf,chosen
    return build

def main():
    parser=ArgumentParser()
    parser.add_argument("--seconds",type=float,default=6)
    parser.add_argument("--window",action="store_true")
    parser.add_argument("--split",action="store_true")
    parser.add_argument("--only",nargs="+")
    args=parser.parse_args()
    data=read(HERE/"cases.json")
    cuts=read(HERE/"cuts.json")
    prior=read(HERE/"families.json")
    dest=HERE/"strengthened.json"
    out=read(dest) if dest.exists() else {}
    images=list(bank.permutation_images())
    with TemporaryDirectory() as d:
        tmp=Path(d)
        tools=masks.compilers(tmp)
        for name,g in data["groups"].items():
            if args.only and name not in args.only:continue
            if args.window and not any(data["roots"][k]["window"] and k not in data["inherited"] for k in g["ranks"]):continue
            if prior[name]["queries"]["0"]["status"]=="excluded" and not prior[name]["witnesses"]:continue
            aligned,core,extras=grouped_inputs(data,g,images)
            negative=exclusions(extras)
            entry=out.setdefault(name,dict(negative=negative,queries={}))
            assert entry["negative"]==negative or list(map(list,negative))==entry["negative"]
            if any(not r["sites"] for r in cuts[name]):
                entry["inherited"]=True
                write(dest,out)
                continue
            build=builder(cuts[name],negative)
            roots=entry["queries"]
            if roots.get("0",{}).get("status") in ("excluded","witness"):continue
            prefixes=[[0]] if not args.split else [[0,1<<j] for j in range(8) if any((1<<j) not in p for p in aligned.values())]
            for prefix in prefixes:
                key=",".join(map(str,prefix))
                old=roots.get(key)
                if old and old["status"] in ("excluded","witness"):continue
                r=masks.query(HERE,tmp,tools,core,args.seconds,extras,prefix,old,builder=build)
                if r["status"]=="witness":
                    r["compatible"]=classify(r["path"],aligned)
                    for pid,desc in r["compatible"].items():
                        if desc["edges"]>=192 or desc["extensions"]:
                            seq=aligned[pid][::-1]+[v+256 for v in r["path"]]
                            if desc["edges"]<192:seq.append(256+desc["extensions"][0])
                            write(HERE/"candidate-192.json",dict(joined=seq,parent=pid,pairs=bank.check_path(seq,9)))
                roots[key]=r
                write(dest,out)
                print(name,len(cuts[name]),prefix,r["status"],flush=True)
                if (HERE/"candidate-192.json").exists():return

if __name__=="__main__":main()
