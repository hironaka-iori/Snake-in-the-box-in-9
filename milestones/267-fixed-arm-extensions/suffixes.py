"""Build a 96-edge partner by its first step and an unrestricted rooted 95-edge suffix."""
from argparse import ArgumentParser
from pathlib import Path
from tempfile import TemporaryDirectory
from families import HERE,read,write,bank,masks
from strengthen import builder,exclusions
from direct import groups

def residual(parents,s):
    foreign={0}|{1<<d for d in range(8) if 1<<d!=s}
    masks_by_parent={k:{x^s for x in set(p[1:])|foreign} for k,p in parents.items() if s not in p[1:]}
    if not masks_by_parent:return None
    common=set.intersection(*masks_by_parent.values())
    assert 0 not in common
    return common,[sorted(F-common) for F in masks_by_parent.values()]

def shifted_cuts(original,common,s):
    # A 96-edge path has a 95-edge prefix, so it must meet every old hit clause.
    return [dict(sites=sorted({v^s for v in c["sites"]}-common)) for c in original if s not in c["sites"]]

def main():
    ap=ArgumentParser()
    ap.add_argument("--seconds",type=float,default=4)
    ap.add_argument("--named",nargs="+")
    ap.add_argument("--split",action="store_true")
    args=ap.parse_args()
    data=read(HERE/"cases.json")
    families=read(HERE/"families.json")
    strong=read(HERE/"strengthened.json")
    direct=read(HERE/"direct-192.json")
    source=read(HERE/"cuts.json")
    file=HERE/"suffixes.json"
    out=read(file) if file.exists() else {}
    images=list(bank.permutation_images())
    with TemporaryDirectory() as d:
        tmp=Path(d)
        tools=masks.compilers(tmp)
        for name,ranks in groups(data,families,strong,direct,False,False):
            if args.named and name not in args.named:continue
            aligned={k:list(bytes(data["roots"][k]["parent"]).translate(images[rank])) for k,rank in ranks.items()}
            if len(next(iter(aligned.values())))!=96:continue
            entry=out.setdefault(name,dict(ranks=ranks,steps={}))
            assert entry["ranks"]==ranks
            for i in range(8):
                s=1<<i
                domains=residual(aligned,s)
                if domains is None:continue
                common,extras=domains
                key=str(s)
                base=entry["steps"].get(key)
                if base and base["status"] in ("excluded","witness"):continue
                cuts=shifted_cuts(source[name],common,s)
                negative=exclusions(extras)
                table=entry.setdefault("children",{}).setdefault(key,{}) if args.split else entry["steps"]
                prefixes=[[0,1<<j] for j in range(8) if (1<<j) not in common and any((1<<j) not in a for a in extras)] if args.split else [[0]]
                for prefix in prefixes:
                    tag=str(prefix[-1]) if args.split else key
                    prev=table.get(tag)
                    if prev and prev["status"] in ("excluded","witness"):continue
                    row=masks.query(HERE,tmp,tools,common,args.seconds,extras,prefix,prev,builder=builder(cuts,negative))
                    if row["status"]=="witness":
                        p=[0]+[v^s for v in row["path"]]
                        parent=next(a for a in aligned.values() if set(a)&set(p)=={0})
                        seq=parent[::-1]+[256+v for v in p]
                        assert len(seq)==193
                        write(HERE/"candidate-192.json",dict(joined=seq,pairs=bank.check_path(seq,9)))
                    table[tag]=row
                    write(file,out)
                    print(name,s,len(common),prefix,row["status"],flush=True)
                    if row["status"]=="witness":return

if __name__=="__main__":main()
