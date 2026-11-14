"""All local checks in the elementary obstruction for retained coordinates 0,1,2."""
from itertools import combinations
from solve import paths

ODD = [1,3,5,7,13,15,17,21,25,27,29,31,37,39,41,45,47,49,51,55,59,61,
       63,65,67,71,75,79,81,83,85,87]
EVEN = [2,6,8,12,14,18,20,22,24,30,32,36,38,42,46,48,52,54,56,58,60,62,
        64,66,68,72,74,76,78,80,82,84,86]


def verify():
    base = [v & 7 for v in paths()[1]]
    groups = [[0]]
    for t in range(1,len(base)):
        if base[t] == base[t-1]:
            groups.append([])
        groups[-1].append(t)
    assert len(groups) == 88

    def cannot_be_neighbors(i,j):
        # A free distance of one would create a forbidden full-cube edge.
        return any(abs(t-u)>1 and base[t]==base[u] for t in groups[i] for u in groups[j])

    def unequal(i,j):
        assert i!=j and (i-j)%2==0
        if any((base[t]^base[u]).bit_count()<=1 for t in groups[i] for u in groups[j]):
            return True
        return any(cannot_be_neighbors(k,y) for x,y in ((i,j),(j,i))
                   for k in (x-1,x+1) if 0<=k<len(groups))

    assert len(set(ODD)) == 32 and all(x%2 for x in ODD)
    assert all(unequal(i,j) for i,j in combinations(ODD,2))
    assert [a for a in ODD if not unequal(23,a)] == [25]
    assert cannot_be_neighbors(20,25) and 23==22+1
    special = {(20,22)}
    for i in (24,48):
        for j in (56,76):
            common = [a for a in ODD if not cannot_be_neighbors(i,a)
                      and not cannot_be_neighbors(j,a)]
            assert len(common)<6
            print(i,j,common)
            special.add((i,j))
    assert len(set(EVEN)) == 33 and all(x%2==0 for x in EVEN)
    assert {pair for pair in combinations(EVEN,2) if not unequal(*pair)} == special
    print("Verified 496 odd pairs, 523 direct even pairs and 5 exceptional even pairs.")


if __name__ == "__main__":
    verify()
