"""Share ladder of count-fixed 7-centre windows: the largest T of LADDER with
"corner share of the 7 centres <= T - 1" UNSAT within tl seconds (lumped count 8 means [8, 21], count 0 means free).
usage: ladder7.py WINDOWS.jsonl OUT.jsonl [tl] [workers]     (WINDOWS: one [dirs, counts] per line)"""
import os, sys, json
from multiprocessing import Pool
import tier7
LADDER = [31, 46, 61, 81, 101, 131, 171, 221, 291, 381]


def one(a):
    (dirs, cnt), tl = a
    b = [(1, 21) if c == 0 else (c, c) if c < 8 else (8, 21) for c in cnt]
    log = []; lb = 0; ub = None
    for T in LADDER:
        st, wit, sec, sel = tier7.test(dirs, b, T, tl)
        log.append([T, st, wit, sec])
        if st == 'UNSAT':
            lb = T
        else:
            if st == 'SAT':
                ub = wit
            break
    return dict(dirs=dirs, counts=cnt, lb=lb, witness=ub, log=log)


if __name__ == '__main__':
    wins = [json.loads(l) for l in open(sys.argv[1])]
    out = sys.argv[2]; tl = float(sys.argv[3]) if len(sys.argv) > 3 else 30
    nw = int(sys.argv[4]) if len(sys.argv) > 4 else 2
    done = set()
    if os.path.exists(out):
        done = {(tuple(r['dirs']), tuple(r['counts'])) for r in map(json.loads, open(out))}
    todo = [(w, tl) for w in wins if (tuple(w[0]), tuple(w[1])) not in done]
    with Pool(nw) as p:
        for r in p.imap_unordered(one, todo):
            with open(out, 'a') as f:
                f.write(json.dumps(r) + '\n')
            print(r, flush=True)
