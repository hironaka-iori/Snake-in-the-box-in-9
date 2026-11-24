"""Seek 192 directly on a shared complement; verify every construction against its actual parent."""
from argparse import ArgumentParser
from pathlib import Path
from tempfile import TemporaryDirectory

from families import HERE, read, write, bank, masks
from rebuild import solve

def groups(data, families, stronger, earlier, window_only, individual):
    finished={k for row in earlier.values() if row['status']=='excluded' for k in row['ranks']}
    for name,g in data["groups"].items():
        extra=stronger.get(name,{})
        if extra.get('inherited') or extra.get('queries',{}).get('0',{}).get('status')=='excluded':
            continue
        done=families.get(name,{})
        if done.get("queries",{}).get("0",{}).get("status")=="excluded" and not done.get("witnesses"):
            continue
        chosen={k:r for k,r in g["ranks"].items() if k not in finished and k not in data["inherited"] and (not window_only or data["roots"][k]["window"])}
        batches=({k:v} for k,v in chosen.items()) if individual else ([chosen] if chosen else [])
        for rs in batches:
            yield name,rs

def main():
    ap=ArgumentParser()
    ap.add_argument("--window",action="store_true")
    ap.add_argument("--individual",action="store_true")
    ap.add_argument("--seconds",type=float,default=8)
    ap.add_argument("--named",nargs="+")
    opt=ap.parse_args()
    data=read(HERE/"cases.json")
    families=read(HERE/"families.json")
    dest=HERE/"direct-192.json"
    ledger=read(dest) if dest.exists() else {}
    stronger=read(HERE/'strengthened.json') if (HERE/'strengthened.json').exists() else {}
    images=list(bank.permutation_images())
    with TemporaryDirectory() as folder:
        tmp=Path(folder)
        tools=masks.compilers(tmp)
        for group,ranks in groups(data,families,stronger,ledger,opt.window,opt.individual):
            if opt.named and group not in opt.named:continue
            label="/".join(sorted(ranks))
            prev=ledger.get(label,{})
            if prev.get("status") in ("witness","excluded"):continue
            align={k:list(bytes(data["roots"][k]["parent"]).translate(images[rank])) for k,rank in ranks.items()}
            blocked=set.intersection(*(set(p[1:]) for p in align.values()))
            n=192-len(next(iter(align.values())))
            ans=solve(HERE,tmp,tools,blocked,n,[0],prev.get("cycles",[]),[],opt.seconds)
            ans.update(group=group,ranks=ranks,blocked=sorted(blocked),length=n)
            if ans["status"]=="witness":
                ans["compatible"]=[k for k,p in align.items() if set(p)&set(ans["path"])=={0}]
                for k in ans["compatible"]:
                    join=align[k][::-1]+[v+256 for v in ans["path"]]
                    write(HERE/"candidate-192.json",dict(joined=join,parent=k,pairs=bank.check_path(join,9)))
                if not ans["compatible"]:
                    ans["status"]="relaxed_witness"
            ledger[label]=ans
            write(dest,ledger)
            print(group,len(ranks),len(blocked),n,ans["status"],flush=True)
            if ans["status"]=="witness":return

if __name__=="__main__":main()
