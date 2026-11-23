"""Reroute the ends of one chord and a separated copy of a certified forbidden anchor."""
import argparse
import json
from pathlib import Path
from search_q9_anchored_sets import search
from search_q9_parent_junctions import check

def cases():
    data=json.loads(Path("q9_onechord_62anchors.json").read_text())
    banks={}
    for entry in data["results"]:
        name=entry["input"]
        if name not in banks:
            banks[name]=[list(map(int,s.split())) for s in Path(name).read_text().splitlines()]
        p=banks[name][entry["row"]]
        edges=[(i,j) for j in range(len(p)) for i in range(j-1) if (p[i]^p[j]).bit_count()==1]
        assert len(edges)==1 and len(p)==len(set(p))==193
        (i,j),=edges
        image,=entry["images"]
        assert len(image)==62 and set(image)<=set(p)
        yield name,entry["row"],p,i,j,image

def main():
    args=argparse.ArgumentParser()
    args.add_argument("--width",type=int,default=6)
    args.add_argument("--target",type=int,default=192)
    args.add_argument("--budget",type=int,default=5000)
    args.add_argument("--limit",type=int,default=0)
    opts=args.parse_args()
    for name,row,p,i,j,image in cases():
        for rank,v in enumerate(sorted(image,key=lambda a:(min((a^p[i]).bit_count(),(a^p[j]).bit_count()),a))):
            if opts.limit and rank>=opts.limit:break
            centers=[0,i,j,p.index(v),len(p)-1]
            fixed={x for k,x in enumerate(p) if min(abs(k-c) for c in centers)>opts.width}
            assert v not in fixed
            status,w=search(fixed,set(p),opts.target,opts.budget,allowed=set(range(512))-{v},at_least=True)
            if w:
                check(w,opts.target)
                assert v not in w and fixed<=set(w)
            print(json.dumps(dict(source=name,row=row,omitted=v,anchors=len(fixed),width=opts.width,
                                  target=opts.target,status=status,witness=w)),flush=True)
            if w and len(w)>=193:return
if __name__=="__main__":main()
