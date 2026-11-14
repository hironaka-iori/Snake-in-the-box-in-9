"""Rebuild the geometric meaning of a pinned 98-edge parent formula on normalized domains."""
from itertools import combinations
import json
import subprocess
from parent_sat import PIN,MILESTONES
from solve import defects


def word(vertex,coords):
    return sum(((vertex>>p)&1)<<i for i,p in enumerate(coords))


def verify(case):
    prefix=PIN+":milestones/"+MILESTONES[case]+"/"
    def get(p):return json.loads(subprocess.check_output(["git","show",prefix+p]))
    source=get("data/lower-dimensional-input.json")["8"]["vertices"]
    m=get(f"data/case-{case}/model.json")
    perms=get(f"data/case-{case}/permutations.json")
    assert len(source)==99 and source[0]==0 and all(x<256 for x in source) and not defects(source)
    z=[word(x,m["base"]) for x in source]
    group=[0]
    for a,b in zip(z,z[1:]):group.append(group[-1]+(a==b))
    assert z==m["z"] and group==m["group"]
    n=group[-1]+1
    assert n==m["variables"] and len(m["block"])==6
    domains=[[v for v in range(64) if v.bit_count()%2==g%2] for g in range(n)]
    domains[0]=[0];domains[1]=[1]
    assert [sum(1<<v for v in d) for d in domains]==m["domains"]
    # Accumulate allowed Hamming distances independently, from every indexed pair.
    table=[[set(range(7)) for j in range(n)] for i in range(n)]
    for i,j in combinations(range(99),2):
        a,b=group[i],group[j];d=(z[i]^z[j]).bit_count()
        table[a][b]={h for h in table[a][b] if (h+d==1 if j==i+1 else h+d>=2)}
    saved={(r["x"],r["y"]):r["rows"] for r in m["constraints"]}
    assert len(saved)==len(m["constraints"])
    for i in range(n):
        assert 0 in table[i][i]
        for j in range(i+1,n):
            lookup=saved.get((i,j))
            for x in domains[i]:
                for y in domains[j]:
                    assert ((x^y).bit_count() in table[i][j])==(lookup is None or bool(lookup[x]>>y&1))
    # Each stored permutation is an actual free-coordinate permutation fixing
    # the first used bit. Its lex constraint therefore preserves an orbit minimum.
    for p in perms:
        assert sorted(p)==list(range(64)) and p[0]==0 and p[1]==1
        images=[p[1<<i] for i in range(6)]
        assert sorted(images)==[1<<i for i in range(6)]
        assert all(p[u]==sum(images[i] for i in range(6) if u>>i&1) for u in range(64))
    assert len(m["nogoods"])==len(m["excluded_witnesses"])
    for assignment,record in zip(m["nogoods"],m["excluded_witnesses"]):
        perm=record["output_to_input"]
        assert sorted(perm)==list(range(8))
        seq=[v^source[-1] for v in reversed(source)] if record["reverse"] else source
        image=[word(v,perm) for v in seq]
        assert image==record["vertices"]
        assert [word(v,m["block"]) for v in image]==[assignment[g] for g in group]
        assert [word(v,m["base"]) for v in image]==z
    return dict(case=case,retained=m["base"],runs=n,pairs=99*98//2,
                equivalent_exclusions=len(m["nogoods"]),coordinate_permutations=len(perms))


if __name__=="__main__":
    import argparse
    parser=argparse.ArgumentParser();parser.add_argument("case",type=int)
    print(verify(parser.parse_args().case))
