"""Rebuild all single omitted intervals of a 190- or 191-edge construction."""
from argparse import ArgumentParser
from collections import Counter
from hashlib import sha256
from struct import pack
from repair_whole import construct,independent,NB
from rebuild_saved import HERE,MS,face,read,save

def main():
    ap=ArgumentParser();ap.add_argument("--length",type=int,default=190)
    ap.add_argument("--first",type=int,default=3);ap.add_argument("--last",type=int,default=9)
    ap.add_argument("--start",type=int,default=0);ap.add_argument("--count",type=int,default=100)
    o=ap.parse_args();hunt=face.dependencies(MS); independent.NEIGHBORS=tuple(NB);independent.CUBE=(1<<512)-1
    n=o.length
    if n==190:parents={k:v["ordered"] for k,v in read(HERE/"growth-from-190.json")["roots"].items()}
    else:parents={k:v["joined"] for k,v in read(HERE/"growth-from-190.json")["children"].items() if v["edges"]==n}
    dest=HERE/f"interval-growth-{n}.json";out=read(dest) if dest.exists() else {}
    for code in sorted(parents)[o.start:o.start+o.count]:
        seed=tuple(parents[code]);bits=[1<<v for v in seed];whole=sum(bits)
        row=out.setdefault(code,dict(seed=seed,budgets={},children={}))
        for length in range(o.first,o.last+1):
            if str(length) in row["budgets"]:continue
            hist=Counter();h=sha256()
            for j in range(len(seed)-length+1):
                omit=tuple(range(j,j+length));kept=whole^sum(bits[t] for t in omit)
                p=construct(seed,whole,bits,omit,n+1,192)
                second=independent._enumerate_mask(whole,kept,n+2,193)
                assert p=={min(s,s[::-1])for s in second}
                h.update(pack("<II",j,len(p)))
                for q in sorted(p):
                    h.update(pack("<"+"H"*len(q),*q));e=len(q)-1;hist[e]+=1
                    assert hunt.original_audit.path_edges(q,9)==e and set(seed)-set(q)==set(seed[j:j+length])
                    sig=hunt.original_audit.shape(q).hex()
                    row["children"].setdefault(sig,dict(edges=e,joined=q,start=j,omissions=length))
                    if e>=192:save(HERE/"candidate-192.json",dict(ordered=q,seed=seed,omitted=omit))
            row["budgets"][str(length)]=dict(equal_buckets=len(seed)-length+1,counts=hist,sha256=h.hexdigest())
            save(dest,out)
        print(code[:16],len(row["budgets"]),"interval sizes",len(row["children"]),"longer shapes",flush=True)
if __name__=="__main__":main()
