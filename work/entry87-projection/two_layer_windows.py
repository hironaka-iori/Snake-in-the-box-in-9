"""Simultaneously change two separated interior sections of a fixed opposite Q7 layer."""
import argparse
from pathlib import Path
from joint_four_repair import sources
from opposite_anchors import arrangements
from one_layer_core import N,study
from solve import defects,save


def reroutes(start,end,length,fixed,forbidden):
    arm=[];occupied=set(fixed)
    def grow(at,left):
        if (at^end).bit_count()>left:return
        if left==1:
            if end in N[at]:yield tuple(arm)
            return
        for w in sorted(N[at]-occupied-{forbidden}):
            expected={at,end} if left==2 else {at}
            if N[w]&occupied!=expected:continue
            occupied.add(w);arm.append(w);yield from grow(w,left-1);arm.pop();occupied.remove(w)
    yield from grow(start,length)


if __name__=="__main__":
    p=argparse.ArgumentParser();p.add_argument("source",type=int);p.add_argument("--orientation",type=int,default=0)
    p.add_argument("--width",type=int,default=10);p.add_argument("--gap",type=int,default=4)
    p.add_argument("--keep",type=int,default=5000);p.add_argument("--nodes",type=int,default=750000);a=p.parse_args()
    q=next(q for i,_,q in sources() if i==a.source);paths=list(arrangements(q))[a.orientation]
    A,_,C,_=paths;out={};nodes=0;tested=0;w=a.width
    for i in range(1,len(C)-2*w-a.gap-1):
        for j in range(i+w+a.gap,len(C)-w-1):
            tested+=1;first=C[:i+1];middle=C[i+w:j+1];last=C[j+w:]
            fixed=set(first+middle+last)
            if tested==1:
                original=tuple(C[i+1:i+w])
                assert original in reroutes(first[-1],middle[0],w,fixed,A[-1])
                assert tuple(C[j+1:j+w]) in reroutes(middle[-1],last[0],w,fixed|set(original),A[-1])
            for length in (w-2,w,w+2,w+4):
                for arm in reroutes(first[-1],middle[0],length,fixed,A[-1]):
                    if arm==tuple(C[i+1:i+w]):continue
                    nodes+=1
                    for length2 in (w-2,w,w+2,w+4):
                        if not 40<=len(C)+length+length2-2*w<=51:continue
                        for arm2 in reroutes(middle[-1],last[0],length2,fixed|set(arm),A[-1]):
                            if arm2==tuple(C[j+1:j+w]):continue
                            c=tuple(first)+arm+tuple(middle)+arm2+tuple(last)
                            assert not defects(c);out[c]=None
    report=study(paths,0,a.keep,a.nodes,True,(out,nodes))
    save(Path(f"two-layer-windows-{a.source}-{a.orientation}-{w}-{a.gap}-{a.keep}-{a.nodes}.json"),
         dict(source=a.source,orientation=a.orientation,width=w,gap=a.gap,window_pairs=tested,**report))
    print(tested,len(out),report["excluded_selected"],report["best_edges"],flush=True)
