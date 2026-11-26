"""Enumerate long Q8 paths after omitting a small number of specified seed sites."""
from argparse import ArgumentParser
from collections import Counter
from hashlib import sha256
from itertools import combinations, permutations, product
from pathlib import Path
import json

HERE=Path(__file__).resolve().parent
MS=HERE.parent
ADJ=[[v^(1<<i) for i in range(8)] for v in range(256)]
N=[sum(1<<u for u in row) for row in ADJ]

def read(p):return json.loads(p.read_bytes())
def write(p,obj):p.write_bytes((json.dumps(obj,separators=(",",":"))+"\n").encode())

def flips(p):
    return bytes((a^b).bit_length()-1 for a,b in zip(p,p[1:]))

def norm(w):
    order=bytes(dict.fromkeys(w))
    return w.translate(bytes.maketrans(order,bytes(range(len(order)))))

def shape(p):
    w=flips(p)
    return min(norm(w),norm(w[::-1])).hex()

def valid(p,d):
    assert len(set(p))==len(p) and all(0<=v<1<<d for v in p)
    for i,v in enumerate(p):
        for j in range(i):
            assert ((p[j]^v).bit_count()==1)==(j+1==i)
    return len(p)*(len(p)-1)//2

def assemble(seed,omit,minimum=93,maximum=98):
    excluded=set(omit)
    blocks=[]
    current=[]
    for i,x in enumerate(seed):
        if i in excluded:
            if current:blocks.append(bytes(current))
            current=[]
        else:current.append(x)
    if current:blocks.append(bytes(current))
    old=sum(1<<v for v in seed)
    kept=sum(1<<v for block in blocks for v in block)
    allowance=maximum+1-kept.bit_count()
    outputs=set()
    def tails(path,used,room,left):
        if left:tails(path,used,room,False)
        elif len(path)>minimum:outputs.add(min(path,path[::-1]))
        if not room:return
        tip=path[0] if left else path[-1]
        for v in ADJ[tip]:
            bit=1<<v
            if bit & (old|used) or N[v]&used!=1<<tip:continue
            nextpath=bytes([v])+path if left else path+bytes([v])
            tails(nextpath,used|bit,room-1,left)
    for ordering in permutations(blocks):
        if len(blocks)>1 and ordering[0]>ordering[-1]:continue
        options=[(b,b[::-1]) if len(b)>1 else (b,) for b in ordering]
        for ordered in product(*options):
            def connect(path,used,room,index):
                if index==len(ordered):
                    tails(path,used,room,True);return
                tip=path[-1];dest=ordered[index][0]
                # Each later gap between distinct old components needs an extra site.
                if (tip^dest).bit_count()-1+len(ordered)-index-1>room:return
                for v in ADJ[tip]:
                    bit=1<<v
                    if not room or bit&(old|used):continue
                    neighbours=N[v]&used
                    if neighbours==((1<<tip)|(1<<dest)):
                        connect(path+bytes([v])+ordered[index],used|bit,room-1,index+1)
                    elif neighbours==1<<tip:
                        connect(path+bytes([v]),used|bit,room-1,index)
            connect(ordered[0],kept,allowance,1)
    return outputs

def sources():
    prior=read(MS/"271-rebuilt-historical-partners/long-joins.json")["witnesses"]
    out={"common92":dict(seed=prior[0]["partner"],reference=prior[0]["joined"],other=prior[0]["parent"])}
    path=HERE/"selected-start.json"
    if path.exists():out.update(read(path))
    return out

def main():
    ap=ArgumentParser()
    ap.add_argument("--source",default="common92");ap.add_argument("--max-omissions",type=int,default=2)
    ap.add_argument("--minimum",type=int,default=93)
    args=ap.parse_args()
    seed=bytes(sources()[args.source]["seed"]);valid(seed,8)
    data={};allshapes={}
    for r in range(args.max_omissions+1):
        histogram=Counter();counts={};digest=sha256()
        for omit in combinations(range(len(seed)),r):
            paths=assemble(seed,omit,args.minimum)
            for p in sorted(paths):
                assert len(p)-1>=args.minimum and len(set(seed)-set(p))==r
                valid(p,8)
                s=shape(p);histogram[len(p)-1]+=1
                row=allshapes.setdefault(s,dict(path=list(p),minimum_omissions=r,placements=0,example_omitted=list(omit)))
                row["placements"]+=1
                digest.update(bytes([r])+bytes(omit)+bytes([len(p)])+p)
            if paths:counts[",".join(map(str,omit))]=len(paths)
        data[str(r)]=dict(histogram=histogram,nonempty=counts,digest=digest.hexdigest())
        print(args.source,r,dict(histogram),len(allshapes),flush=True)
        write(HERE/(args.source+"-paths.json"),dict(seed=list(seed),minimum=args.minimum,maximum=98,levels=data,shapes=allshapes))

if __name__=="__main__":main()
