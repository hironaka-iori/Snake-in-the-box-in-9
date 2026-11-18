"""Witnessed per-shape minima (ceilings) of the combined 7-window weight W12 = sum(24 alpha + share12)
and of share12 alone, from real-snake / adversary seeds improved by annealing (sa.c).
usage: ceil7.py SHAPES.jsonl OUT.jsonl [workers] [iters] [mode: comb|share]"""
import sys, os, json, subprocess
from multiprocessing import Pool
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE)
from combined import exact, window_from_dirs
from sawit import check
import seeds as SD

SEEDS = {}
def build_seeds(shapes):
    want = {tuple(s) for s in shapes}
    out = {s: [] for s in want}
    srcs = [('bank', p, S) for p, S in SD.bank_paths()]
    for nm in ('adversary224.json', 'adversary208.json'):
        try:
            srcs += [(nm[:12], p, S) for p, S in SD.adversary_paths(nm)]
        except Exception as e:
            print('no', nm, e)
    for src, p, S in srcs:
        for c, sel in SD.occurrences(p, S):
            if c in out:
                out[c].append((src, sel))
    return out

def val(w, sel, wA):
    A, SH = exact(w, sel, 12)
    return wA * sum(A) + sum(SH), A, SH

def one(args):
    dirs, sl, wA, iters = args
    w = window_from_dirs(list(dirs))
    ball = None
    sc = []
    for src, sel in sl:
        sel = [v for v in sel if min(bin(v ^ x).count('1') for x in w) <= 4]
        v, _, _ = val(w, sel, wA); sc.append((v, src, sel))
    sc.sort(key=lambda t: t[0])
    pick = sc[:3] + [t for t in sc if t[1] != 'bank'][:2]
    best = None
    seed_best = None
    for v, src, sel in sc:
        if check(w, sel):
            seed_best = (v, src); break
    for j, (v, src, sel) in enumerate(pick):
        for rep in range(2):
            inp = f"{len(w)} {' '.join(map(str, w))} 4 12 {wA} {iters} {7*j+rep+1} 0\n{len(sel)} {' '.join(map(str, sel))}\n"
            env = dict(os.environ, T0='40', T1='0.5')
            out = subprocess.run([os.path.join(HERE, 'sa')], input=inp, capture_output=True, text=True, env=env).stdout.split('\n')
            if not out[1].strip():
                continue
            s2 = list(map(int, out[1].split()))
            if not check(w, s2):
                continue
            v2, A, SH = val(w, s2, wA)
            if best is None or v2 < best['value']:
                best = dict(value=v2, alpha=A, share=SH, src=src, sel=s2)
    return dict(dirs=list(dirs), wA=wA, nseeds=len(sl), seed_best=seed_best, best=best)

if __name__ == '__main__':
    shapes = [json.loads(l)['dirs'] for l in open(sys.argv[1])]
    out = sys.argv[2]; nw = int(sys.argv[3]) if len(sys.argv) > 3 else 4
    iters = int(sys.argv[4]) if len(sys.argv) > 4 else 2000000
    wA = 24 if (len(sys.argv) <= 5 or sys.argv[5] == 'comb') else 0
    done = set()
    if os.path.exists(out):
        done = {(tuple(json.loads(l)['dirs']), json.loads(l)['wA']) for l in open(out)}
    shapes = [s for s in shapes if (tuple(s), wA) not in done]
    sd = build_seeds(shapes)
    todo = [(s, sd[tuple(s)], wA, iters) for s in shapes]
    with Pool(nw) as p:
        for r in p.imap_unordered(one, todo):
            with open(out, 'a') as f: f.write(json.dumps(r) + '\n')
            b = r['best']
            print(r['dirs'], r['nseeds'], r['seed_best'], b and b['value'], b and sum(b['alpha']), b and sum(b['share']), flush=True)
