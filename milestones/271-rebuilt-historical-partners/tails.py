"""Rebuild free ends of the longest joined paths while preserving one complete Q8 parent."""
from argparse import ArgumentParser
from collections import Counter
from hunt import HERE, cases, read, write, original_audit


FULL=(1<<256)-1
NEIGHBOURS=[sum(1<<(v^(1<<j)) for j in range(8)) for v in range(256)]
EVEN=sum(1<<v for v in range(256) if v.bit_count()%2==0)


def rebuild_tail(parent,seed,keep,incumbent,cap):
    path=seed[:keep+1]
    assert incumbent[:keep+1]==path
    available=FULL ^ sum(1<<v for v in parent)
    for u,v in zip(path,path[1:]):
        assert NEIGHBOURS[u] & available & (1<<v)
        available &= ~NEIGHBOURS[u]
    nodes=0
    best=list(incumbent)
    stopped=False
    def visit(allowed):
        nonlocal nodes,best,stopped
        if nodes>=cap:stopped=True;return
        nodes+=1
        if len(path)>len(best):best=path[:]
        if len(parent)+len(best)-1>=192:return
        tip=path[-1]
        moves=allowed & NEIGHBOURS[tip]
        if not moves:return
        opposite=(allowed &(EVEN if tip.bit_count()%2 else ~EVEN)).bit_count()
        same=allowed.bit_count()-opposite
        if len(path)+min(2*opposite,2*same+1)<=len(best):return
        next_allowed=allowed & ~NEIGHBOURS[tip]
        while moves:
            bit=moves & -moves
            moves^=bit
            path.append(bit.bit_length()-1)
            visit(next_allowed)
            path.pop()
            if stopped or len(parent)+len(best)-1>=192:return
    visit(available)
    joined=parent[::-1]+[256+v for v in best]
    length=original_audit.path_edges(joined,9)
    return best,dict(kept_partner_edges=keep,nodes=nodes,complete=not stopped and length<192,
                     joined_edges=length)


def main():
    cli=ArgumentParser()
    cli.add_argument("--cap",type=int,default=125000)
    cli.add_argument("--minimum",type=int,default=178)
    cli.add_argument("--cuts",type=int,nargs="+",default=[12,20,28,36])
    args=cli.parse_args()
    findings={}
    extra={}
    for f in sorted(HERE.glob("matched-*.json")):
        if not f.stem.rsplit("-",1)[-1].isdigit():continue
        for tag,row in read(f).items():
            if row["best"]:extra.setdefault(tag.split(":")[0],set()).add(tuple(row["best"]["B"]))
    verified=HERE/"retained-site-replay.json"
    source=cases()
    if verified.exists():
        for k,r in read(verified).items():
            p=source[k]["parent"]
            extra.setdefault(k,set()).add(tuple(v-256 for v in r["joined"][len(p):]))
    for k,r in sorted(source.items(),key=lambda kv:-kv[1]["best"]["edges"]):
        if r["best"]["edges"]<args.minimum:continue
        parent=r["parent"]
        seeds={tuple(r["best"]["B"]),*(tuple(p) for p in r["history"].values())}
        seeds.update(extra.get(k,set()))
        if len(r["placement"]["partner"])+len(parent)-1>=args.minimum:
            seeds.add(tuple(r["placement"]["partner"]))
        result=[]
        for seed in sorted(seeds,key=lambda p:(-len(p),p)):
            seed=list(seed)
            longest=seed
            records=[]
            for cut in sorted(set(args.cuts)):
                longest,outcome=rebuild_tail(parent,seed,max(0,len(seed)-1-cut),longest,args.cap)
                records.append(outcome)
                if outcome["joined_edges"]>=192:break
            q=parent[::-1]+[256+v for v in longest]
            result.append(dict(start=seed,partner=longest,joined=q,rounds=records))
            if len(q)>=193:
                write(HERE/"candidate-192.json",{k:q})
                break
        findings[k]=result
        best=max(len(s["joined"])-1 for s in result)
        print(k[:10],r["best"]["edges"],best,sum(a["nodes"] for s in result for a in s["rounds"]),flush=True)
        if best>=192:break
    write(HERE/"tails.json",dict(minimum=args.minimum,cap_per_prefix=args.cap,cuts=args.cuts,roots=findings))

if __name__=="__main__":
    main()
