"""Recover SAT witnesses in the original coordinates and compare their interval shapes."""
from collections import Counter, defaultdict
from itertools import permutations
from hunt import HERE, cases, original_audit, read, write
from exchange import input_paths


def extensions(p):
    tip=p[-1]
    return [v for i in range(9) if (v:=tip^(1<<i)) not in p
            and all((v^w).bit_count()!=1 for w in p[:-1])]


def collect():
    roots=cases(); groups=read(HERE/"groups.json")
    maps=list(permutations(range(8))); rows={}
    for f in sorted(HERE.glob("queries-*.json")):
        n=int(f.stem.rsplit("-",1)[-1])
        for job in read(f).values():
            g=groups[job["group"]]
            for address,r in job["rows"].items():
                if r["status"]!="witness":continue
                for k,path in r["joins"].items():
                    axes=maps[g["ranks"][k]]
                    q=[(v&256)+sum(1<<i for i,b in enumerate(axes) if v&(1<<b)) for v in path]
                    p=roots[k]["parent"];b=[v-256 for v in q[len(p):]]
                    assert q==p[::-1]+[256+v for v in b] and b[0]==0 and set(p)&set(b)=={0}
                    assert original_audit.path_edges(q,9)==n
                    word=original_audit.shape(q).hex()
                    row=dict(parent_key=k,parent=p,partner=b,joined=q,edges=n,
                             prior_edges=roots[k]["best"]["edges"],unordered_pairs=n*(n+1)//2,
                             canonical_transition_word=word,group=job["group"],prefix=address,
                             legal_tip_extensions=[extensions(q[::-1]),extensions(q)])
                    rows[k+":"+word]=row
    return rows


def review():
    rows=collect()
    words={r["canonical_transition_word"] for r in rows.values()}
    lengths={r["edges"] for r in rows.values()}; sources=Counter(); matches=defaultdict(list)
    for label,q in input_paths():
        sources[len(q)-1]+=1
        for n in lengths:
            for start in range(len(q)-n):
                w=original_audit.shape(q[start:start+n+1]).hex()
                if w in words:matches[w].append(dict(source=label,start=start))
    write(HERE/"long-joins.json",dict(witnesses=list(rows.values()),different_shapes=len(words),
          archive_sources=sources,interval_matches={w:matches[w] for w in sorted(words)}))
    print("witnesses",[(r["parent_key"][:10],r["edges"],r["legal_tip_extensions"]) for r in rows.values()],
          "shapes",len(words),"archived intervals",sum(map(len,matches.values())))


if __name__=="__main__":
    review()
