"""Independent check: selected set is ONE induced path in Q9; report its alpha sequence and the
alphas at the window centres 1,3,7 (window 0,1,3,7,6|15)."""
import json, sys, itertools
PAIRS = list(itertools.combinations(range(9), 2))

def order_path(S):
    S = set(S)
    adj = {x: [x ^ 1 << k for k in range(9) if (x ^ 1 << k) in S] for x in S}
    assert all(len(a) <= 2 for a in adj.values()), 'degree>2'
    ends = [x for x in S if len(adj[x]) == 1]
    assert len(ends) == 2, ('ends', len(ends))
    seq = [ends[0]]; prev = None
    while True:
        nxt = [y for y in adj[seq[-1]] if y != prev]
        if not nxt:
            break
        prev = seq[-1]; seq.append(nxt[0])
    assert len(seq) == len(S), 'not connected (or cycle component present)'
    return seq

def alphas(seq):
    S = set(seq)
    return [sum(all(w not in S for w in (x ^ 1 << i, x ^ 1 << j, x ^ 1 << i ^ 1 << j)) for i, j in PAIRS) for x in seq]

if __name__ == '__main__':
    for path in sys.argv[1:]:
        for r in json.load(open(path)):
            if 'selected' not in r:
                continue
            seq = order_path(r['selected'])
            a = alphas(seq)
            pos = {x: i for i, x in enumerate(seq)}
            win = [0, 1, 3, 7, 6 if r['shape'] == 'repeated' else 15]
            ii = [pos[w] for w in win]
            assert ii == list(range(ii[0], ii[0] + 5)) or ii == list(range(ii[0], ii[0] - 5, -1)), ii
            got = [a[pos[c]] for c in (1, 3, 7)]
            print(r['radius'], r['shape'], r['alpha'], '-> genuine snake, edges', len(seq) - 1,
                  'window alphas', got, 'OK' if got == r['alpha'] else 'MISMATCH', ' T/v=%.2f' % (sum(a) / len(a)))
