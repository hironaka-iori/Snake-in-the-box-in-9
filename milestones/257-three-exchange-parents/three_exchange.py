"""Exact three-exchange shell with all orders and both endpoint attachments free."""
from hashlib import sha256
from itertools import combinations
from math import comb
from pathlib import Path
import json
import sys

HERE=Path(__file__).resolve().parent
MS=HERE.parent
sys.path.insert(0,str(MS/"256-two-exchange-parents"))
from enumerate_shell import mask, NEIGH, search, check_path, word, digest, read


def main():
    class_id=sys.argv[1]
    radius=int(sys.argv[2]) if len(sys.argv)>2 else 3
    if radius not in (2,3):
        raise ValueError("This round covers two and three simultaneous replacements")
    if class_id=="distant":
        source=MS/"254-distant-arm-partners/parity-families.json"
        from enumerate_arms import SEED
        seed=read(source)["shapes"][SEED]
    else:
        source=MS/"256-two-exchange-parents"/("shell-"+class_id+".json")
        seed=read(source)["reference"]
    side=set(seed[1::2])
    outside=[v for v in range(256) if (v^seed[1]).bit_count()%2==0 and v not in side]
    other=[v for v in range(256) if (v^seed[1]).bit_count()%2]
    if len(side)!=48 or len(outside)!=80: raise ValueError("Reference sizes")
    pair_counts,positives,shapes=[],[],{}
    overall=0

    for removed in combinations(sorted(side),radius):
        retained=tuple(sorted(side-set(removed)))
        fixed=mask(retained)
        layers=[0,0,0]
        for y in other:
            degree=(NEIGH[y]&fixed).bit_count()
            if degree<=2: layers[degree]|=1<<y
        zeros,ones,twos=layers
        candidates=[a for a in outside if (NEIGH[a]&(zeros|ones)).bit_count()>=2]
        retained_neighbours=[NEIGH[v] for v in retained]
        passing=0

        def extend(index, chosen, empty, single, double, selected_neighbours):
            nonlocal passing
            for j in range(index,len(candidates)-(radius-1-len(chosen))):
                a=candidates[j]
                n=NEIGH[a]
                if (n&(empty|single)).bit_count()<2:
                    continue
                new_one=(single&~n)|(empty&n)
                new_two=(double&~n)|(single&n)
                legal=new_one|new_two
                if any((neighbours&legal).bit_count()<2 for neighbours in selected_neighbours):
                    continue
                inserted=chosen+(a,)
                if len(inserted)<radius:
                    extend(j+1,inserted,empty&~n,new_one,new_two,selected_neighbours+[n])
                elif new_one.bit_count()>=2:
                    passing+=1
                    target=sorted((*retained,*inserted))
                    paths,_=search(target)
                    if paths:
                        entries=[]
                        for path in sorted(paths):
                            check_path(path)
                            if len(path)!=97 or sorted(path[1::2])!=target:
                                raise ValueError("Invalid contraction")
                            key=sha256(word(path)).hexdigest()
                            shapes.setdefault(key,path)
                            entries.append(dict(shape=key,vertices=path))
                        positives.append(dict(removed=removed,inserted=inserted,paths=entries))
        if len(candidates)>=radius:
            extend(0,(),zeros,ones,twos,retained_neighbours)
        pair_counts.append(passing)
        overall+=passing
    paths_prev=[(MS/"253-repeated-segment-growth/closure.json","paths"),
                (MS/"254-distant-arm-partners/parity-families.json","shapes"),
                (MS/"255-parity-exchange-arms/focus-closure.json","paths")]
    known=set().union(*(read(p)[k] for p,k in paths_prev))
    counts=dict(removed_subsets=len(pair_counts),all_classes=comb(48,radius)*comb(80,radius),
                pass_supply=overall,viable_classes=len(positives),
                labelled=sum(len(r["paths"]) for r in positives),shapes=len(shapes),new_shapes=len(set(shapes)-known))
    result=dict(class_id=class_id,radius=radius,reference=seed,reference_shape=sha256(word(seed)).hexdigest(),
                counts=counts,pass_supply_by_lexicographic_removed_subset=pair_counts,
                new_shapes=sorted(set(shapes)-known),positive_classes=positives,shapes=shapes,
                sha256={p.relative_to(MS).as_posix():digest(p) for p in
                        [source,Path(__file__),Path(sys.modules["enumerate_shell"].__file__),
                         Path(sys.modules["enumerate_arms"].__file__),*(p for p,k in paths_prev)]})
    dest=HERE if radius==3 else HERE/"two-exchange-comparison"
    dest.mkdir(exist_ok=True)
    (dest/("shell-"+class_id+".json")).write_text(json.dumps(result,separators=(",",":"))+"\n",encoding="utf-8",newline="\n")
    print(class_id,counts,flush=True)

if __name__=="__main__": main()
