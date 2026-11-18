"""Sweep: CP-SAT minimum of W12 = sum_7 (wA alpha + share12) for every 7-centre shape (1 worker each).
usage: cpbatch.py SHAPES.jsonl OUT.jsonl tl wA procs"""
import sys, os, json
from multiprocessing import Pool
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE)
def one(a):
    dirs, tl, wA = a
    from cpmin import minimize, window_from_dirs
    from sawit import check
    r = minimize(dirs, tl=tl, wA=wA, workers=1)
    if 'sel' in r:
        r['valid_cnf'] = bool(check(window_from_dirs(list(dirs)), r['sel']))
    return r
if __name__ == '__main__':
    shapes = [json.loads(l)['dirs'] for l in open(sys.argv[1])]
    out, tl, wA, P = sys.argv[2], float(sys.argv[3]), int(sys.argv[4]), int(sys.argv[5])
    done = set()
    if os.path.exists(out):
        done = {tuple(json.loads(l)['dirs']) for l in open(out)}
    todo = [(d, tl, wA) for d in shapes if tuple(d) not in done]
    with Pool(P, maxtasksperchild=1) as p:
        for r in p.imap_unordered(one, todo):
            with open(out, 'a') as f: f.write(json.dumps(r) + '\n')
            print(r['dirs'], r.get('status'), r.get('value'), r.get('lb'), r.get('valid_cnf'), flush=True)
