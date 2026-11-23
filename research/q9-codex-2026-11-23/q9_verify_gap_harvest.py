import json
from pathlib import Path
def decode(w):
    p=[0]
    for c in w:p.append(p[-1]^(1<<int(c)))
    return p
def valid(p):
    return len(p)==len(set(p)) and all(0<=v<512 for v in p) and all(((x^p[j]).bit_count()==1)==(i+1==j) for i,x in enumerate(p) for j in range(i+1,len(p)))
def key(w):
    def norm(w):
        order=list(dict.fromkeys(w))
        return tuple(order.index(c) for c in w)
    return min(norm(w),norm(w[::-1]))
refs={key(w.strip()) for w in open("q9_gap_known189.words")}
refs190={key(w.strip()) for w in open("q9_gap_known190.words")}
paths=Path("q9_gap_harvest_189.words").read_text().splitlines()
assert len(paths)==len(set(map(key,paths))) and not set(map(key,paths))&refs
hits={190:set(),191:set(),192:set()};fresh190=set();sets=set()
for w in paths:
    p=decode(w);assert len(p)==190 and valid(p)
    sets.update(tuple(sorted(s)) for s in (p[::2],p[1::2]))
    frontier={tuple(p)}
    for k in (190,191,192):
        layer=set()
        for q in frontier:
            for rev in (0,1):
                r=q[::-1] if rev else q
                for a in range(9):
                    y=r[-1]^(1<<a)
                    if y in r or any(((x^y).bit_count()==1) for x in r[:-1]):continue
                    new=r+(y,);layer.add(new[::-1] if rev else new)
        for q in layer:
            assert valid(q)
            s=key(tuple(a^b for a,b in zip(q,q[1:])));hits[k].add(s)
            if k==190 and s not in refs190:fresh190.add(s)
            if k==192:print("FOUND",*q)
        frontier=layer
with open("q9_gap_harvest_halves.txt","w") as out:
    for s in sorted(sets):print(*s,file=out)
print(json.dumps(dict(new_189=len(paths),reference_189=len(refs),extensions={k:len(h) for k,h in hits.items()},outside_reference190=len(fresh190),halfsets=len(sets)),indent=2))
