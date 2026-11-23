"""Enumerate every possible lower occupancy containing one of the catalogue paths."""
from pathlib import Path
from collections import Counter
from itertools import combinations
import json
from q9_classify_record_donor_windows import canonical
from q9_rigid_facet_ports import word_path
D=Path("q9_catalogue_four_cross")
def main():
    D.mkdir(exist_ok=True)
    bank=Path("q8_catalogue_96_98.words").read_text().split()
    norm={canonical(w):i for i,w in enumerate(bank)}
    assert len(norm)==len(bank)==753
    neighbors=[{v^1<<d for d in range(8)} for v in range(256)]
    rows=[];spec=[];raw=Counter();extra_edges=Counter()
    for i,w in enumerate(bank):
        arm=word_path(w);f=set(arm)
        assert len(f)==len(arm) and all(((v^u).bit_count()==1)==(j+1==k) for k,v in enumerate(arm) for j,u in enumerate(arm[:k]))
        E=sorted(v for v in range(256) if v not in f and not neighbors[v].intersection(arm[1:-1]))
        extra_edges[sum(v in neighbors[u] for u,v in combinations(E,2))]+=1
        for mask in range(1<<len(E)):
            S=f|{x for j,x in enumerate(E) if mask>>j&1}
            if any(len(neighbors[x]&S)>2 for x in S):continue
            component=[arm[0]];covered=set(component)
            for x in component:
                more=(neighbors[x]&S)-covered;component.extend(more);covered.update(more)
            islands=S-covered
            assert all(not neighbors[x]&S for x in islands)
            if len(islands)>2:continue
            ends=[x for x in component if len(neighbors[x]&S)==1]
            if len(ends)!=2:continue
            q=[ends[0]];rem=covered-set(q)
            while rem:
                x,=neighbors[q[-1]]&rem;q.append(x);rem.remove(x)
            shape=canonical("".join(str((u^v).bit_length()-1) for u,v in zip(q,q[1:])))
            assert shape in norm
            rows.append([i,norm[shape],sorted(S-f),sorted(islands)])
            raw[len(q)-1,len(islands)]+=1
        eg=sorted(x for x in range(256) if x not in f and not neighbors[x]&f)
        for u,v in combinations(eg,2):
            if v not in neighbors[u]:
                spec.append(dict(index=i,ends=[u,v],parity=(u^v).bit_count()%2,word=w))
    (D/"lower.json").write_text(json.dumps(rows,separators=(",",":")))
    (D/"cases.jsonl").write_text("".join(json.dumps(dict(case=j,**r))+"\n" for j,r in enumerate(spec)))
    with (D/"even.in").open("w") as out:
        for j,r in enumerate(spec):
            if not r["parity"]:
                a=word_path(r["word"]);u,v=r["ends"]
                print(j,3,1,u,len(a),*a,1,v,file=out)
    print(json.dumps(dict(catalogue=len(bank),lower=len(rows),histogram={str(k):v for k,v in raw.items()},extras_edges=dict(extra_edges),four_crossings=Counter(r["parity"] for r in spec))))
if __name__=="__main__":main()
