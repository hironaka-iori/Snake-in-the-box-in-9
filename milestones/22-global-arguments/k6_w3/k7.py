"""Seven-centre plain tests on the minimum witnessed cycle of a ceil.py run.
For each cycle position j, both orientations of the 6-window key K6[j] are extended by one direction
d and one count a such that the last 7 directions / 6 counts give K6[j+1]; every such extension is a
7-window that a lift of the cycle may contain.  The cycle dies at k = 7 if, at some position, all
extensions are plain-UNSAT.   usage: k7.py F PEN    (new plain calls: data/plain_k6w3.jsonl)"""
import sys, os, json
from k6w3lib import *
from ceil import setup, min_cycle
from refine import key as rkey, induced, canon

AV = [(1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 21)]


def main():
    F, pen = int(sys.argv[1]), int(sys.argv[2])
    G, P, O, sub = setup()
    c = min_cycle(G, P, O, sub, F, pen)
    K6 = c['k6']; n = len(K6)
    print('cycle', c['lam'], 'witnessed', c['witnessed'], [keystr(k) for k in K6], flush=True)
    res = []
    for j in range(n):
        k, t = K6[j], K6[(j + 1) % n]
        ext = set()
        for ds, al in ((list(k[0]), list(k[1])), (list(reversed(k[0])), list(reversed(k[1])))):
            for d in range(9):
                for a in AV:
                    if induced(tuple(ds) + (d,)) and rkey(tuple(ds[1:]) + (d,), tuple(al[1:]) + (a,)) == t:
                        ext.add(rkey(tuple(ds) + (d,), tuple(al) + (a,)))
        sts = []
        for k7 in sorted(ext):
            if k7 not in P.st:
                P.test(k7, 300)
            sts.append((keystr(k7), P.st.get(k7)))
        dead = bool(sts) and all(s == 'UNSAT' for _, s in sts)
        print(j, keystr(k), '->', sts, 'DEAD' if dead else '', flush=True)
        res.append(dict(pos=j, k6=keystr(k), k7=sts, dead=dead))
    json.dump(dict(cycle=[keystr(k) for k in K6], lam=str(c['lam']), positions=res),
              open(os.path.join(DATA, f'k7_F{F}p{pen}.json'), 'w'), indent=1)


if __name__ == '__main__':
    main()
