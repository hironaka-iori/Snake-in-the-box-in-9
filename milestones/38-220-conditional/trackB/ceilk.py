"""Shape-only automaton with per-shape combined floors for k-centre windows (L = k+1 directions):
witnessed ceiling loop, as ceilloop.py.  usage: ceilk.py L rounds tl target"""
import json, os, sys
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE)
from shapegraph import shapes, graph
import seeds as SD
from combined import exact, window_from_dirs
from sawit import check
import ceilloop as CL

def main(L, rounds, tl, target):
    WF = os.path.join(HERE, 'data', f'witness_L{L}.jsonl'); CL.WFILE = WF
    S = shapes(L); E = graph(S); want = set(S)
    U = CL.load(); best = {}
    if not U:
        for p, Sset in SD.bank_paths():
            for c, sel in SD.occurrences(p, Sset, L):
                if c not in want: continue
                w = window_from_dirs(list(c))
                sel = [v for v in sel if min(bin(v ^ x).count('1') for x in w) <= 4]
                A, SH = exact(w, sel, 12); v = 24 * sum(A) + sum(SH)
                if c not in best or v < best[c][0]: best[c] = (v, sel)
        for c, (v, sel) in best.items():
            r = dict(dirs=list(c), value=v, src='bank', sel=sel); CL.add(r); U[c] = r
    print('shapes', len(S), 'edges', sum(len(v) for v in E.values()), 'witnessed', len(U), flush=True)
    tried = {}
    for rd in range(rounds):
        cyc, mu = CL.min_cycle(E, U, S)
        if cyc is None: print('no cycle among witnessed shapes'); return
        print(f'round {rd}: min cycle mean {mu:.1f} len {len(cyc)}', [''.join(map(str, c)) for c in cyc][:12],
              [U[c]['value'] for c in cyc][:12], flush=True)
        if mu < target: print(f'BELOW {target}: dead'); return
        cand = sorted(cyc, key=lambda c: (tried.get(c, 0), -U[c]['value']))[0]
        tried[cand] = tried.get(cand, 0) + 1
        print('  improve', cand, U[cand]['value'], '->', CL.improve(cand, U, tl), flush=True)

if __name__ == '__main__':
    main(int(sys.argv[1]), int(sys.argv[2]), float(sys.argv[3]), float(sys.argv[4]))
