"""One level per shape: is 'corner share sum of the 7 centres <= T-1' UNSAT for every 8-direction shape?
usage: corner7_at.py SHAPES.jsonl OUT.jsonl T [tl] [workers]"""
import os, sys, json
from multiprocessing import Pool
import corner7


def one(a):
    d, T, tl = a
    st, wit, sec = corner7.test(d, T, tl)
    return dict(dirs=d, T=T, result=st, witness=wit, seconds=sec)


if __name__ == '__main__':
    shapes = [json.loads(l)['dirs'] for l in open(sys.argv[1])]
    out, T = sys.argv[2], int(sys.argv[3])
    tl = float(sys.argv[4]) if len(sys.argv) > 4 else 300
    nw = int(sys.argv[5]) if len(sys.argv) > 5 else 3
    done = set()
    if os.path.exists(out):
        done = {(tuple(r['dirs']), r['T']) for r in map(json.loads, open(out))}
    todo = [(d, T, tl) for d in shapes if (tuple(d), T) not in done]
    with Pool(nw) as p:
        for r in p.imap_unordered(one, todo):
            with open(out, 'a') as f:
                f.write(json.dumps(r) + '\n')
            print(r, flush=True)
