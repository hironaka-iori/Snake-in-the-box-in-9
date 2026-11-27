"""Enumerate Q9 paths near a verified 189, allowing arbitrary coordinate crossings."""
from argparse import ArgumentParser
from array import array
from collections import Counter
from hashlib import sha256
from itertools import combinations,permutations,product
from struct import pack
from rebuild_saved import HERE,MS,face,read,save,resolve,literal,transform,isometry
import replay_near as independent

NEAR=[[v^(1<<i) for i in range(9)] for v in range(512)]
NB=[sum(1<<u for u in adj) for adj in NEAR]

def construct(seed,old,bits,omit,minimum,limit):
    cut=(-1,*omit,len(seed));blocks=[seed[i+1:j] for i,j in zip(cut,cut[1:]) if j>i+1]
    kept=old^sum(bits[i] for i in omit); budget=limit+1-kept.bit_count();out=set()
    def tails(path,used,left,room):
        if left:tails(path,used,False,room)
        elif len(path)>minimum:out.add(min(path,path[::-1]))
        if room==0:return
        tip=path[0] if left else path[-1];flag=1<<tip
        for u in NEAR[tip]:
            b=1<<u
            if b&(old|used) or NB[u]&used!=flag:continue
            tails((u,)+path if left else path+(u,),used|b,left,room-1)
    for order in permutations(blocks):
        if len(order)>1 and order[0]>order[-1]:continue
        for pieces in product(*[(b,b[::-1]) if len(b)>1 else (b,) for b in order]):
            def bridge(path,used,room,i):
                if i==len(pieces):tails(path,used,True,room);return
                target=pieces[i][0];tip=path[-1]
                if room<(target^tip).bit_count()-1+len(pieces)-i-1:return
                for u in NEAR[tip]:
                    flag=1<<u
                    if not room or flag&(old|used):continue
                    adjacent=NB[u]&used
                    if adjacent==(1<<tip)|(1<<target):
                        bridge(path+(u,)+pieces[i],used|flag,room-1,i+1)
                    elif adjacent==1<<tip:bridge(path+(u,),used|flag,room-1,i)
            bridge(pieces[0],kept,budget,1)
    return out

def main():
    ap=ArgumentParser();ap.add_argument("--roots",nargs="+",default=["f89b","948d"])
    ap.add_argument("--omissions",type=int,default=2);ap.add_argument("--limit",type=int,default=192)
    ap.add_argument("--minimum",type=int,default=190);opts=ap.parse_args()
    parents=read(HERE/"opposite/plan.json")["roots"]
    placements=read(HERE/"saved-placements.json")["roots"]
    hunt=face.dependencies(MS);independent.NEIGHBORS=tuple(NB);independent.CUBE=(1<<512)-1
    dest=HERE/"whole-path-repairs.json"
    ledger=read(dest) if dest.exists() else {}
    for pre in opts.roots:
        k=resolve(parents,pre);p=parents[k];cross=p["raw_endpoint"]
        seed=tuple(transform(placements[k]["best"]["joined"],isometry(p["normalized"],literal(p))))
        assert hunt.original_audit.path_edges(seed,9)==189
        bits=[1<<v for v in seed];old=sum(bits);comparison=sha256()
        hist=Counter();positive=Counter();answers={};total=0
        for count in range(opts.omissions+1):
            for omitted in combinations(range(len(seed)),count):
                keep=old^sum(bits[i] for i in omitted)
                got=construct(seed,old,bits,omitted,opts.minimum,opts.limit)
                ref=independent._enumerate_mask(old,keep,opts.minimum+1,opts.limit+1)
                assert got=={min(seq,seq[::-1]) for seq in ref},(k,omitted)
                comparison.update(bytes([count,*omitted]));comparison.update(pack("<I",len(got)))
                total+=1
                if got:positive[count]+=1
                for seq in sorted(got):
                    comparison.update(pack("<"+"H"*len(seq),*seq))
                    edges=len(seq)-1;hist[edges]+=1
                    assert hunt.original_audit.path_edges(seq,9)==edges
                    assert set(seed)-set(seq)=={seed[i] for i in omitted}
                    sig=hunt.original_audit.shape(seq).hex()
                    if sig not in answers:
                        axes=[(u^v).bit_length()-1 for u,v in zip(seq,seq[1:])]
                        answers[sig]=dict(edges=edges,omitted=list(omitted),joined=seq,
                                          crossings_once=[i for i in range(9) if axes.count(i)==1])
                    if edges>=192:save(HERE/"candidate-192.json",dict(ordered=seq,source=k,omitted=omitted))
        ledger[k]=dict(start=seed,omissions=opts.omissions,minimum=opts.minimum,maximum_examined=opts.limit,
                       equal_buckets=total,buckets_with_outputs=positive,counts=hist,sha256=comparison.hexdigest(),shapes=answers)
        save(dest,ledger)
        print(k[:10],"buckets",total,"joined-edge counts",hist,"distinct shapes",len(answers),flush=True)
if __name__=="__main__":main()
