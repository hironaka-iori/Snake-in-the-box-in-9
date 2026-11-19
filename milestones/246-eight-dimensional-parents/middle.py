"""Recombine outer paths around a 47-edge Q7 middle and lift twice."""
from collections import Counter, defaultdict
from hashlib import sha256
import json
from compare import HERE, signature, verify


def cuts(path):
    for axis in range(8):
        split=[i for i,(u,v) in enumerate(zip(path,path[1:])) if u^v==1<<axis]
        if len(split)!=2 or split[1]-split[0]!=48:
            continue
        a,b=split
        mask=(1<<axis)-1
        p=[(v&mask)|((v>>(axis+1))<<axis) for v in path]
        yield axis,p[a::-1],p[a+1:b+1],p[b+1:]


def maps(first,second):
    for backwards in (False,True):
        dest=second[::-1] if backwards else second
        axes={u^v:a^b for u,v,a,b in zip(first,first[1:],dest,dest[1:])}
        if len(axes)!=7 or len(set(axes.values()))!=7:
            continue
        table=[0]
        for i in range(7):
            table.extend([v^axes[1<<i] for v in table])
        offset=table[first[0]]^dest[0]
        table=[v^offset for v in table]
        if [table[v] for v in first]==dest:
            yield table,backwards


def bits(path):
    return sum(1<<v for v in path)


N=[bits(v^(1<<i) for i in range(7)) for v in range(128)]


def border(path):
    closed=bits(path)
    for v in path:
        closed |= N[v]
    return closed


def main():
    comp=(HERE/"comparison.json").read_bytes()
    donors=(HERE/"donors.json").read_bytes()
    pairs=json.loads(comp)["one_crossing_pairs"]
    core=next(cuts(pairs[0]["long"]))[2]
    ports=[set(),set()]
    sources=0
    for record in json.loads(donors)["shapes"]:
        for _,a,m,b in cuts(record["path"]):
            for lut,backwards in maps(m,core):
                sources+=1
                for side,arm in enumerate((a,b)):
                    out=tuple(lut[v] for v in arm)
                    slot=side^int(backwards)
                    if set(out)&set(core)!={core[0 if slot==0 else -1]}:
                        raise ValueError("Additional intersection with middle")
                    ports[slot].add(out)
    source_ports=list(map(len,ports))
    for arcs in ports:
        for arm in tuple(arcs):
            banned=border(arm[:-1])|bits(arm)|bits(core)
            free=N[arm[-1]] & ~banned
            while free:
                bit=free&-free
                free^=bit
                arcs.add(arm+(bit.bit_length()-1,))
    arms={}
    right=[(b,bits(b)) for b in sorted(ports[1])]
    for a in sorted(ports[0]):
        blocked=border(a)
        for b,mask in right:
            length=len(a)+len(b)+47
            if length<92 or blocked&mask:
                continue
            path=list(a[::-1])+[128+v for v in core]+list(b)
            verify(path,False)
            arms[a,b]=length

    def placed(middle):
        result={}
        for lut,_ in maps(core,middle):
            for (a,b),length in arms.items():
                x=tuple(lut[v] for v in a)
                y=tuple(lut[v] for v in b)
                result[x,y]=(length,bits(x+y),[lut[v] for v in core])
        return result

    layouts={}
    for row in pairs:
        for axis,_,m,_ in cuts(row["long"]):
            for axis2,_,n,_ in cuts(row["short"]):
                if axis==axis2 and signature(m)==signature(core)==signature(n):
                    layouts.setdefault((tuple(m),tuple(n)),[]).append(row["seed"])
    results=[]
    witness=None
    reference=next(iter(layouts))
    for (m,n),seeds in layouts.items():
        if set(m)&set(n):
            raise ValueError("Middle paths meet")
        first,second=placed(list(m)),placed(list(n))
        by_end=defaultdict(list)
        for (x,y),(length,mask,mid) in second.items():
            for end in (x[-1],y[-1]):
                by_end[end].append((x,y,length,mask,mid))
        lengths=Counter()
        best=None
        best_length=-1
        def rooted(x,y,mid,q):
            path=list(x[::-1])+[128+z for z in mid]+list(y)
            return path if path[0]==q else path[::-1]
        for (x,y),(length,mask,mid) in first.items():
            for q in (x[-1],y[-1]):
                for u,v,other,other_mask,other_mid in by_end[q]:
                    if mask&other_mask != 1<<q:
                        continue
                    joined=length+other+1
                    lengths[joined]+=1
                    if joined>best_length:
                        best_length=joined
                        a,b=rooted(x,y,mid,q),rooted(u,v,other_mid,q)
                        best=a[::-1]+[256+t for t in b]
                        verify(best,False)
                        if len(best)!=joined+1:
                            raise ValueError("Join length")
                        if joined>=192:
                            witness=best
        isometry=None
        for swap,(a,b) in enumerate((reference,reference[::-1])):
            for lut,reverse_first in maps(list(m),list(a)):
                image=tuple(lut[v] for v in n)
                if image==b or image==b[::-1]:
                    isometry=dict(swap=swap,reverse_first=reverse_first,reverse_second=image==b[::-1],
                                  translation=lut[0],axis_images=[lut[1<<i]^lut[0] for i in range(7)])
                    break
            if isometry:
                break
        results.append(dict(seeds=seeds,middles=[m,n],isometry_to_first=isometry,first=len(first),second=len(second),
                            lengths=lengths,best=best))
    m,n=map(list,reference)
    exchanges=[]
    for lut,backwards in maps(m,n):
        exchanges.append(dict(translation=lut[0],axis_images=[lut[1<<i]^lut[0] for i in range(7)],
                              reversed=backwards,involution=all(lut[lut[v]]==v for v in range(128)),
                              displacement=Counter((v^lut[v]).bit_count() for v in range(128))))
    output=dict(inputs=[sha256(comp).hexdigest(),sha256(donors).hexdigest()],aligned_cuts=sources,
                ports_from_donors=source_ports,ports_with_new_tip=list(map(len,ports)),
                arm_lengths=Counter(arms.values()),core=core,layouts=results,middle_exchange_maps=exchanges,witness=witness)
    (HERE/"middle.json").write_text(json.dumps(output,separators=(",",":"))+"\n",encoding="utf-8",newline="\n")
    print("outer pieces",source_ports,"with end additions",list(map(len,ports)),"arms",dict(Counter(arms.values())))
    print("labelled middle pairs",len(results),"best lengths",[max(map(int,r["lengths"]),default=-1) for r in results])


if __name__=="__main__":
    main()
