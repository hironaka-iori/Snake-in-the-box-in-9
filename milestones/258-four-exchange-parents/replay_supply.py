"""Independent coverage using the old sites that must be deleted to permit each insertion."""
from collections import defaultdict,Counter
from hashlib import sha256
from itertools import combinations,product
from math import comb
from pathlib import Path
import sys
import json

HERE=Path(__file__).resolve().parent
N=[tuple(v^(1<<d) for d in range(8)) for v in range(256)]
M=[sum(1<<u for u in n) for n in N]


def prerequisites(base,outside,radius):
    # Two eventual path neighbours of a new vertex must each keep at most one old neighbour.
    by_removed=defaultdict(int)
    for a in outside:
        requirements=set()
        for y,z in combinations(N[a],2):
            neighbours=[set(N[b])&base for b in (y,z)]
            if any(len(row)>radius+1 for row in neighbours): continue
            for i,j in product(*(list(row) or [None] for row in neighbours)):
                forced=(neighbours[0]-{i}) | (neighbours[1]-{j})
                if len(forced)<=radius: requirements.add(tuple(sorted(forced)))
        for required in requirements: by_removed[required]|=1<<a
    return by_removed


def examine(shell):
    data=json.loads(shell.read_bytes())
    radius=data["radius"]
    p=data["reference"]
    base=set(p[1::2])
    opposite=[v for v in range(256) if (v^p[1]).bit_count()%2]
    outside=sorted(set(range(256))-base-set(opposite))
    demands=prerequisites(base,outside,radius)
    total=0
    viable_drops=0
    considered=0
    transcript=sha256()
    for removed in combinations(sorted(base),radius):
        allowed=0
        for size in range(radius+1):
            for subset in combinations(removed,size):
                allowed|=demands.get(subset,0)
        if allowed.bit_count()<radius: continue
        viable_drops+=1
        candidates=[]
        while allowed:
            bit=allowed & -allowed
            candidates.append(bit.bit_length()-1)
            allowed^=bit
        fixed=base-set(removed)
        bitmask=sum(1<<u for u in fixed)
        # Labels of initial degree above two never become usable during insertion.
        low=[(y,(M[y]&bitmask).bit_count()) for y in opposite if (M[y]&bitmask).bit_count()<=2]
        levels=tuple(sum(1<<y for y,d in low if d==i) for i in range(3))
        # A retained site with exactly two usable labels needs both of them.
        # If either label already has degree two, any insertion adjacent to it is impossible.
        usable_before=levels[1]|levels[2]
        protected=0
        for u in fixed:
            labels=M[u]&usable_before
            if labels.bit_count()<2: break
            if labels.bit_count()==2: protected|=labels&levels[2]
        else:
            candidates=[a for a in candidates if not (M[a]&protected)]
            if len(candidates)<radius: continue
            for added in combinations(candidates,radius):
                considered+=1
                zero,one,two=levels
                for a in added:
                    n=M[a]
                    zero,one,two=zero&~n,(one&~n)|(zero&n),(two&~n)|(one&n)
                usable=one|two
                if (one.bit_count()>=2 and all((M[a]&usable).bit_count()>=2 for a in added)
                        and all((M[u]&usable).bit_count()>=2 for u in fixed)):
                    total+=1
                    transcript.update(bytes((*removed,*added)))
    if total!=data["supply_survivors"] or transcript.hexdigest()!=data["survivor_digest"]:
        raise ValueError(("Independent supply classification differs",shell.name,total))
    return dict(shell_sha256=sha256(shell.read_bytes()).hexdigest(),candidate_sets=comb(48,radius)*comb(80,radius),
                removed_sets=comb(48,radius),possible_removed_sets=viable_drops,candidates_after_prerequisites=considered,
                physical_survivors=total,ordered_survivor_sha256=transcript.hexdigest())


if __name__=="__main__":
    for arg in sys.argv[1:]:
        source=Path(arg).resolve()
        result=examine(source)
        result["replay_source_sha256"]=sha256(Path(__file__).read_bytes()).hexdigest()
        (source.parent/("coverage-"+source.stem+".json")).write_text(json.dumps(result,indent=2)+"\n",encoding="utf-8",newline="\n")
        print(source.stem,result["possible_removed_sets"],result["candidates_after_prerequisites"],result["physical_survivors"],flush=True)
