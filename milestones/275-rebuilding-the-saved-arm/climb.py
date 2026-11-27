"""Continue every discovered repair shape by one or two further site replacements."""
from argparse import ArgumentParser
from collections import Counter
from hashlib import sha256
from itertools import combinations
from struct import pack
from repair_whole import NEAR,NB,construct,independent
from rebuild_saved import HERE,MS,face,read,save

def main():
    ap=ArgumentParser()
    ap.add_argument("--length",type=int,default=190)
    ap.add_argument("--omissions",type=int,default=2)
    ap.add_argument("--first",type=int,default=0);ap.add_argument("--count",type=int,default=64)
    opt=ap.parse_args();n=opt.length;hunt=face.dependencies(MS)
    independent.NEIGHBORS=tuple(NB);independent.CUBE=(1<<512)-1
    source=read(HERE/"whole-path-repairs.json")
    parents={}
    for k,data in source.items():
        for code,row in data["shapes"].items():
            if row["edges"]==n:
                obj=parents.setdefault(code,dict(path=row["joined"],first_roots=[]))
                obj["first_roots"].append(k)
    if n>190:
        prev=read(HERE/f"growth-from-{n-1}.json")
        for code,row in prev["children"].items():
            if row["edges"]==n:parents.setdefault(code,dict(path=row["joined"],first_roots=row["first_roots"]))
    dest=HERE/f"growth-from-{n}.json"
    data=read(dest) if dest.exists() else dict(roots={},children={})
    for code in sorted(parents)[opt.first:opt.first+opt.count]:
        if code in data["roots"] and data["roots"][code]["omissions"]>=opt.omissions:continue
        obj=parents[code];q=tuple(obj["path"])
        assert hunt.original_audit.shape(q).hex()==code and hunt.original_audit.path_edges(q,9)==n
        bits=[1<<v for v in q];old=sum(bits);h=sha256();tot=Counter();examples={};cases=0
        for count in range(opt.omissions+1):
            for omitted in combinations(range(len(q)),count):
                kept=old^sum(bits[i] for i in omitted)
                got=construct(q,old,bits,omitted,n+1,192)
                independent_paths=independent._enumerate_mask(old,kept,n+2,193)
                assert got=={min(p,p[::-1]) for p in independent_paths}
                h.update(bytes([count,*omitted]));h.update(pack("<I",len(got)));cases+=1
                for p in sorted(got):
                    h.update(pack("<"+"H"*len(p),*p));e=len(p)-1;tot[e]+=1
                    assert hunt.original_audit.path_edges(p,9)==e and set(q)-set(p)=={q[i] for i in omitted}
                    s=hunt.original_audit.shape(p).hex()
                    examples.setdefault(s,list(omitted))
                    c=data["children"].setdefault(s,dict(edges=e,joined=p,first_roots=[],from_parents=[]))
                    if code not in c["from_parents"]:c["from_parents"].append(code)
                    c["first_roots"]=sorted(set(c["first_roots"])|set(obj["first_roots"]))
                    if e>=192:save(HERE/"candidate-192.json",dict(edges=e,path=p,previous=q,omitted=omitted))
        data["roots"][code]=dict(ordered=q,first_roots=obj["first_roots"],equal_buckets=cases,omissions=opt.omissions,
                                 sha256=h.hexdigest(),counts=tot,children=examples)
        save(dest,data)
        print(code[:16],cases,dict(tot),len(examples),flush=True)
    print("Continuations",len(data["roots"]),Counter(r["edges"] for r in data["children"].values()),flush=True)
if __name__=="__main__":main()
