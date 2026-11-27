"""Independently enumerate every 98-edge path missing few vertices from the Carlson arm."""
from argparse import ArgumentParser
from hashlib import sha256
import sys
from inputs276 import HERE,MS,read,save,canonical,valid
sys.path.insert(0,str(MS/"274-rebuilding-near-a-fixed-arm"))
from near import assemble
from replay_near import iter_buckets

def main():
    ap=ArgumentParser();ap.add_argument("--radius",type=int,default=2);a=ap.parse_args()
    inputs=read(HERE/"input-arms.json");base=inputs["known_endpoints"]["0"]["parent"]
    levels={};shapes={}
    for deleted,bag in iter_buckets(base,a.radius,98,98):
        row=levels.setdefault(len(deleted),dict(masks=0,nonempty=0,labelled=0,examples=[]))
        second=assemble(base,deleted,98,98);actual={bytes(p) for p in bag}
        assert actual==second;row["masks"]+=1
        if actual:
            row["nonempty"]+=1;row["labelled"]+=len(actual);row["examples"].append([list(deleted),len(actual)])
        for p in actual:
            assert valid(p,8)==4851 and set(base)-set(p)=={base[i] for i in deleted}
            s=canonical(p);shapes.setdefault(s,dict(path=list(p),minimum_omissions=len(deleted)))
    save(HERE/("site-neighbours-%d.json"%a.radius),dict(levels=levels,shapes=shapes,
        input_sha256=sha256((HERE/"input-arms.json").read_bytes()).hexdigest()))
    print("Omission levels",[(k,v["masks"],v["labelled"]) for k,v in levels.items()],"shapes",len(shapes),flush=True)
if __name__=="__main__":main()
