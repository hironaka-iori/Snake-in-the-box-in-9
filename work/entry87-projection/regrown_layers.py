"""Use the independently checked local Q7 path closures as additional layer menus."""
import argparse,json
from pathlib import Path
from four_layer_bank import menus,test
from solve import save


if __name__=="__main__":
    p=argparse.ArgumentParser();p.add_argument("sizes",nargs=4,type=int)
    p.add_argument("--nodes",type=int,default=1500000000);p.add_argument("--mode",choices=("expanded","direct","mixed"),default="expanded")
    a=p.parse_args();base=json.loads(Path("highdim-seven-39.json").read_text())["forms"];origin={s.encode():v for s,v in base.items()}
    direct={};sources=[]
    for f in sorted(Path(".").glob("seven-regrow-*json")):
        r=json.loads(f.read_text());sources.append(f.name);bag=direct.setdefault(r["size"],{})
        for s in r["forms"]:bag[s.encode()]=f.name
    expand=origin.copy()
    for size,forms in direct.items():
        if size>=min(a.sizes):expand.update(forms)
    chosen=[]
    for j,size in enumerate(a.sizes):
        if a.mode=="direct":
            bank=origin|direct.get(size,{})
        elif a.mode=="mixed" and j in (1,3):
            bank=origin
        else:bank=expand
        chosen.append(menus(bank,size))
    print("Forms",list(map(len,chosen)),flush=True)
    r=test(chosen,Path("four-layer-bank.exe").resolve(),a.nodes)
    r.update(sizes=a.sizes,classes=list(map(len,chosen)),sources=sources,mode=a.mode)
    save(Path(f"regrown-layers-{'-'.join(map(str,a.sizes))}-{a.mode}-{a.nodes}.json"),r)
    print(r["status"],r["nodes"],flush=True)
