"""List necessary Q7 layer counts for a Q9 path with 221 edges and a pair used 18 times."""
from collections import Counter
from itertools import product

from q9_tight_interface_search import SIDES


def upper_edges(components):
    small = (0, 50, 50, 50, 52, 51, 50, 49, 48)
    if components < len(small):
        return small[components]
    return min(48, 64-components)


def compatible(internal, components, crossings):
    for (a,b), cross in zip(SIDES,crossings):
        if cross == 0:
            continue
        if max(internal[a],internal[b]) == 52 and min(internal[a],internal[b]) >= 51:
            return False
        for i,j in ((a,b),(b,a)):
            if cross >= 4 and internal[i] == 52 and internal[j] >= 50 and internal[j]+components[j] >= 54:
                return False
    return True


def patterns(odd):
    endpoints = (0, 3 if odd else 0)
    # The four layers have 203 internal edges, at most 52 each.
    for internal in product(range(47,53), repeat=4):
        if sum(internal) != 203:
            continue
        allowed = [[c for c in range(1,20) if e <= upper_edges(c)] for e in internal]
        for components in product(*allowed):
            if sum(components) != 19 or components[0]+components[3] != 10:
                continue
            a,b,c,d = (2*n-endpoints.count(i) for i,n in enumerate(components))
            for first in range(min(a,b)+1):
                crossings = (first,a-first,b-first,c-a+first)
                if min(crossings) < 0 or crossings[2]+crossings[3] != d:
                    continue
                # A spanning subgraph of the four-cycle needs at least three sides.
                if sum(x > 0 for x in crossings) < 3:
                    continue
                count = crossings[0]+crossings[3]
                if count%2 != odd or min(count,18-count) < 3:
                    continue
                if compatible(internal,components,crossings):
                    yield internal,components,crossings


if __name__ == '__main__':
    for odd in (True,False):
        modes = Counter(tuple(sorted(e)) for e,_,_ in patterns(odd))
        print('odd' if odd else 'even',sum(modes.values()), sorted(modes.items()))

