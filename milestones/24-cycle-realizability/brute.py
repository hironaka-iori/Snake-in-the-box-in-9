"""Independent brute-force check of unroll.c (no symmetry reduction, pure Python):
enumerate every concrete continuation of the shape walk by canon() of the window
directly (all 9 labels), keep induced paths, return the maximum number of transitions."""
import sys
from shapes import canon


def induced_ext(vs, w):
    if w in vs:
        return False
    return all(bin(u ^ w).count('1') >= 2 for u in vs[:-1])


def brute(states, phase=0, cap=10 ** 7):
    p = len(states)
    seq = list(states[phase % p])
    vs = [0]
    for d in seq:
        w = vs[-1] ^ (1 << d)
        assert induced_ext(vs, w)
        vs.append(w)
    best = [0]
    cnt = [0]

    def go(n):
        cnt[0] += 1
        assert cnt[0] < cap
        best[0] = max(best[0], n)
        want = tuple(states[(phase + n + 1) % p])
        for d in range(9):
            if canon(seq[-6:] + [d]) != want:
                continue
            w = vs[-1] ^ (1 << d)
            if not induced_ext(vs, w):
                continue
            seq.append(d); vs.append(w)
            go(n + 1)
            seq.pop(); vs.pop()
    go(0)
    return best[0], cnt[0]


if __name__ == '__main__':
    import json
    states = [tuple(s) for s in json.loads(sys.argv[1])]
    for ph in range(len(states)):
        print(ph, brute(states, ph))
