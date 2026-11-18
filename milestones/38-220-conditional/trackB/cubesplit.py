"""Cube split of a level item  NOT(sum alpha <= a and share12 <= cap)  (track B, cheaper encoding).
Per-centre alpha totalizers give literals [alpha_c >= t].  Each cube fixes, for every centre,
alpha_c <= t or alpha_c >= t+1 (threshold t, 2^k cubes; optional second split).  Cubes are solved
under assumptions in ONE incremental CaDiCaL (learnt clauses and cycle cuts shared); a cube whose
lower alpha bounds already exceed a is closed by the at-most constraint, a cube of low alpha is
closed by plain reasoning, a cube of high alpha needs only a small share.  Every cube UNSAT =>
item UNSAT (the cubes cover all alpha vectors).  usage: cubesplit.py DIRS Y a t [tl_per_cube]"""
import sys, os, json, time, itertools
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE)
from levels import LevelEnc
from combined import ws, window_from_dirs, exact
import wincert
from pysat.solvers import Cadical153

class CubeEnc(LevelEnc):
    def build_share(self):
        super().build_share()
        X, w = self.var, self.window; self.ge = []
        for ci in range(1, len(w) - 1):
            c = w[ci]
            used = {(c ^ w[ci - 1]).bit_length() - 1, (c ^ w[ci + 1]).bit_length() - 1}
            al = [-X[c ^ 1 << a ^ 1 << b] for a, b in itertools.combinations(range(9), 2)
                  if a not in used and b not in used]
            self.ge.append(self.totalizer(al, up=True, down=True))   # ge[i][t] <-> alpha_i >= t

LOG = None
def run(dirs, Y, a, t, tl=600, M=12):
    w = window_from_dirs(list(dirs)); k = len(w) - 2
    cap = Y - 1 - 2 * M * a
    t0 = time.time()
    enc = CubeEnc(w, 4, M, cap, a)
    build = time.time() - t0
    stats = dict(trivial=0, unsat=0, sat=0, timeout=0); slow = []
    with Cadical153(bootstrap_with=enc.clauses) as s:
        for bits in itertools.product((0, 1), repeat=k):
            # quick count closure: lower bound of alpha sum
            if sum((t + 1) if b else 1 for b in bits) > a:
                stats['trivial'] += 1; continue
            assum = [enc.ge[i][t + 1] if b else -enc.ge[i][t + 1] for i, b in enumerate(bits)]
            c0 = time.time()
            while True:
                s.conf_budget(20000)
                r = s.solve_limited(assumptions=assum)
                if r is None:
                    if time.time() - c0 > tl: stats['timeout'] += 1; slow.append((bits, 'TO')); break
                    continue
                if not r:
                    stats['unsat'] += 1; break
                m = s.get_model(); sel = [v for v in enc.ball if m[enc.var[v] - 1] > 0]
                cyc = wincert.cycles_of(sel)
                if not cyc:
                    A, SH = exact(w, sel, M)
                    stats['sat'] += 1
                    return dict(dirs=list(dirs), Y=Y, a=a, t=t, result='SAT', alpha=A, share=SH,
                                W=24 * sum(A) + sum(SH), stats=stats, seconds=round(time.time() - t0, 1))
                for cy in cyc:
                    enc.add_cycle_cut(cy); s.add_clause(enc.clauses[-1])
            dt = time.time() - c0
            if dt > 20: slow.append((bits, round(dt, 1)))
            n = sum(stats.values())
            if LOG:
                print(json.dumps(dict(cube=''.join(map(str, bits)), sec=round(dt, 2), n=n, stats=stats,
                                      el=round(time.time() - t0))), file=LOG, flush=True)
    return dict(dirs=list(dirs), Y=Y, a=a, t=t, result='UNSAT' if not stats['timeout'] else 'PARTIAL',
                stats=stats, slow=slow[:20], build=round(build, 1), seconds=round(time.time() - t0, 1))

if __name__ == '__main__':
    dirs = json.loads(sys.argv[1]); Y, a, t = int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4])
    tl = float(sys.argv[5]) if len(sys.argv) > 5 else 600
    LOG = open(os.path.join(HERE, 'data', f'cube_{a}_{t}.log'), 'w')
    r = run(dirs, Y, a, t, tl)
    with open(os.path.join(HERE, 'data', 'cubesplit.jsonl'), 'a') as f: f.write(json.dumps(r) + '\n')
    print(json.dumps(r), flush=True)
