"""Change the two fixed runs before freely rebuilding their opposite face."""
import argparse
import json
from pathlib import Path
from three_cross_faces import catalogue, decide, normalize
from solve import save


def tips(path, length):
    if length == 0:
        yield path
        return
    tail = path[-1]
    for j in range(8):
        new = tail ^ (1 << j)
        if all((new ^ v).bit_count() >= 2 for v in path[:-1]):
            yield from tips(path+[new], length-1)


def key(a,b):
    return min(normalize(x,y) for first,second in ((a,b),(b,a))
               for x in (first,first[::-1]) for y in (second,second[::-1]))


def menu(rows,source):
    initial = {row["forest"] for row in rows}
    a,b = rows[source]["forest"]
    new = {}
    for first in (a,a[::-1]):
        for second in (b,b[::-1]):
            for left,right in ((1,1),(1,2),(2,1)):
                for x in tips(list(first[:-1]),left):
                    forbidden = {v for u in x for v in [u,*[u^(1<<j) for j in range(8)]]}
                    for y in tips(list(second[:-1]),right):
                        if not forbidden.isdisjoint(y):
                            continue
                        shape = key(x,y)
                        if shape not in initial:
                            new[shape]=dict(forest=shape, source=source)
    return sorted(new.values(),key=lambda r:(-sum(map(len,r["forest"])),r["forest"]))


if __name__ == "__main__":
    parser=argparse.ArgumentParser()
    parser.add_argument("source",type=int)
    parser.add_argument("--start",type=int,default=0)
    parser.add_argument("--stop",type=int,default=0)
    parser.add_argument("--target",type=int,default=193,choices=(192,193))
    parser.add_argument("--budget",type=int,default=400000)
    args=parser.parse_args()
    originals=catalogue()
    if args.source == -1:
        by_shape={}
        for s in range(len(originals)):
            for row in menu(originals,s):
                shape=row["forest"]
                by_shape.setdefault(shape,dict(forest=shape,sources=[]))["sources"].append(s)
        rows=sorted(by_shape.values(),key=lambda r:(-sum(map(len,r["forest"])),r["forest"]))
    else:
        rows=menu(originals,args.source)
    if not args.stop:
        save(Path(f"three-regrow-{args.source}-menu.json"),rows)
        print(len(rows))
    for i in range(args.start,min(args.stop,len(rows))):
        decide(rows[i],f"r{args.source}-{i}",args.target,args.budget,new=(args.target==192))
