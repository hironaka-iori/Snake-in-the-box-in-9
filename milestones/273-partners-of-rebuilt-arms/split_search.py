"""Search smaller subfamilies when an unrestricted group remains unresolved."""
from argparse import ArgumentParser
from search_partners import HERE,read,transport271,catalogue,hunt,cases

if __name__=="__main__":
    ap=ArgumentParser()
    ap.add_argument("--target",type=int,default=192)
    ap.add_argument("--seconds",type=float,default=5)
    ap.add_argument("--depth",type=int,default=0)
    ap.add_argument("--only",type=int,nargs="+",required=True)
    ap.add_argument("--chunk",type=int,default=2)
    opt=ap.parse_args()
    opt.parents=[96];opt.deficit=True;opt.controls=False;opt.improve_only=False
    transport271.catalogue=catalogue
    hunt.HERE=HERE;hunt.R270=HERE;hunt.cases=cases
    align=hunt.aligned
    groups=read(HERE/"groups.json")
    max_size=max(len(groups[i]["ranks"]) for i in opt.only)
    for offset in range(0,max_size,opt.chunk):
        def subgroup(g,roots,images):
            entries=list(align(g,roots,images).items())
            return dict(entries[offset:offset+opt.chunk])
        hunt.aligned=subgroup
        hunt.proof_search(opt)
        if (HERE/"candidate-192.json").exists():break
