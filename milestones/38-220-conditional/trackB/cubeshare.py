"""Uniform share floor 'share12 of the k centres >= T' (counts free) by a per-centre alpha cube split.
Same CNF as wincert_share.ShareEncoding(window, free counts, radius, 12, T-1) plus per-centre alpha
totalizers (definitional, so every cube refutation is a refutation of the base CNF + cube units).
mode 'mono': one solve.  mode 'cube': 2^k cubes alpha_c <= t / >= t+1 under assumptions in one
incremental CaDiCaL (learnt clauses and lazy cycle cuts shared).
usage: cubeshare.py DIRS T mode t tl_per_cube R"""
import sys, os, json, time, itertools
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE)
from combined import ws, window_from_dirs, exact
import wincert
from pysat.solvers import Cadical153

class Enc(ws.ShareEncoding):
    def build_share(self):
        super().build_share()
        X, w = self.var, self.window; self.ge = []
        for ci in range(1, len(w) - 1):
            c = w[ci]
            used = {(c ^ w[ci - 1]).bit_length() - 1, (c ^ w[ci + 1]).bit_length() - 1}
            al = [-X[c ^ 1 << a ^ 1 << b] for a, b in itertools.combinations(range(9), 2)
                  if a not in used and b not in used]
            self.ge.append(self.totalizer(al, up=True, down=True))

def solve_assum(s, enc, assum, tl):
    c0 = time.time()
    while True:
        s.conf_budget(20000)
        r = s.solve_limited(assumptions=assum)
        if r is None:
            if time.time() - c0 > tl: return 'TIMEOUT', None
            continue
        if not r: return 'UNSAT', None
        m = s.get_model(); sel = [v for v in enc.ball if m[enc.var[v] - 1] > 0]
        cyc = wincert.cycles_of(sel)
        if not cyc: return 'SAT', sel
        for cy in cyc:
            enc.add_cycle_cut(cy); s.add_clause(enc.clauses[-1])

LOG = None
def run(dirs, T, mode, t, tl, R=4):
    w = window_from_dirs(list(dirs)); k = len(w) - 2
    t0 = time.time(); enc = Enc(w, [None] * k, R, 12, T - 1)
    out = dict(dirs=list(dirs), T=T, mode=mode, t=t, R=R)
    with Cadical153(bootstrap_with=enc.clauses) as s:
        if mode == 'mono':
            st, sel = solve_assum(s, enc, [], tl); out.update(result=st)
            if sel: out['share'] = ws.share_exact(w, sel)
        else:
            st_all = dict(UNSAT=0, SAT=0, TIMEOUT=0); times = []
            for bits in itertools.product((1, 0), repeat=k):     # high-alpha cubes first
                c0 = time.time()
                st, sel = solve_assum(s, enc, [enc.ge[i][t + 1] if b else -enc.ge[i][t + 1] for i, b in enumerate(bits)], tl)
                st_all[st] += 1; times.append(round(time.time() - c0, 2))
                if LOG: print(json.dumps(dict(cube=''.join(map(str, bits)), st=st, sec=times[-1], el=round(time.time() - t0), counts=st_all)), file=LOG, flush=True)
                if st == 'SAT':
                    out.update(share=ws.share_exact(w, sel), cube=''.join(map(str, bits))); break
            out.update(result='SAT' if st_all['SAT'] else ('UNSAT' if not st_all['TIMEOUT'] else 'PARTIAL'),
                       counts=st_all, max_cube=max(times), cubes_over_10s=sum(1 for x in times if x > 10))
    out['seconds'] = round(time.time() - t0, 1)
    return out

if __name__ == '__main__':
    dirs = json.loads(sys.argv[1]); T = int(sys.argv[2]); mode = sys.argv[3]
    t = int(sys.argv[4]); tl = float(sys.argv[5]); R = int(sys.argv[6]) if len(sys.argv) > 6 else 4
    LOG = open(os.path.join(HERE, 'data', f'cs_{T}_{mode}{t}.log'), 'w')
    r = run(dirs, T, mode, t, tl, R)
    with open(os.path.join(HERE, 'data', 'cubeshare.jsonl'), 'a') as f: f.write(json.dumps(r) + '\n')
    print(json.dumps(r), flush=True)
