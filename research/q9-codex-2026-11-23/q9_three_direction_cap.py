"""Optimize the eight Q6 edge counts under the verified local contact rule."""
from itertools import product


def connects(edges):
    seen = {0}
    queue = [0]
    for v in queue:
        for axis in (1,2,4):
            w = v ^ axis
            high,low = max(edges[v],edges[w]),min(edges[v],edges[w])
            if w not in seen and (high <= 25 or low <= 23):
                seen.add(w)
                queue.append(w)
    return len(seen) == len(edges)


def cap():
    # If any Q6 layer is empty, the sum is at most 7*26 = 182.
    # For the other cases raising counts below 23 to 23 preserves the allowed
    # interface graph and can only increase the objective.
    possible = [e for e in product((23,24,25,26),repeat=8) if connects(e)]
    upper = max(map(sum,possible))
    return upper, sorted({tuple(sorted(e)) for e in possible if sum(e)==upper})


if __name__ == "__main__":
    print(*cap())
