"""Put rooted fixed arms in common coordinates and record their shared blocked vertices."""
from itertools import permutations
from pathlib import Path
import importlib.util
import sys

from catalogue import HERE, MS, read, write
from growth import bank

spec=importlib.util.spec_from_file_location("intersection_columns",MS/"260-donor-intersections/replay.py")
counter=importlib.util.module_from_spec(spec)
spec.loader.exec_module(counter)


def best_alignment(parent, maps):
    live=bank.ALL_MAPS
    for level in reversed(counter.columns(maps[v] for v in parent[1:])):
        take=live & level
        if take:
            live=take
    return (live & -live).bit_length()-1


def pack(parents, images, minimum):
    remaining=dict(sorted(parents.items()))
    packed=[]
    while remaining:
        first=next(iter(remaining))
        shared=set(remaining.pop(first)[1:])
        placed={first:0}
        while remaining:
            flags=bank.allowed_maps([0]+sorted(set(range(1,256))-shared),images)
            choices=[]
            for k,p in remaining.items():
                rank=best_alignment(p,flags)
                overlap=shared.intersection(bytes(p[1:]).translate(images[rank]))
                choices.append((len(overlap),k,rank,overlap))
            count,k,rank,overlap=max(choices,key=lambda t:(t[0],t[1]))
            if count<minimum:
                break
            shared=overlap
            placed[k]=rank
            del remaining[k]
        packed.append(dict(blocked=sorted(shared),ranks=placed))
    return packed


def main():
    roots=read(HERE/"parents.json")["parents"]
    images=list(bank.permutation_images())
    result={}
    for end in ("published","opposite"):
        parents={k:r["parent"] for k,r in roots.items() if r["from_191"] and bool(r["partners"])==(end=="published")}
        result[end]=pack(parents,images,0)[0]
        assert len(result[end]["ranks"])==5
        print(end,len(result[end]["blocked"]))
    write(HERE/"aligned.json",result)

if __name__=="__main__":
    main()
