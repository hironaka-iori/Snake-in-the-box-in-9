"""Split of the combined floor W = sum_7 (24 alpha + share12) >= Y by window alpha sum:
W >= Y  <=>  for every a <= ceil(Y/24)-1:  NOT( sum alpha <= a  and  share12 <= Y-1-24a ).
Each item is a ShareEncoding (counts free) + an at-most-a constraint on the 147 singleton
literals.  usage: levels.py DIRS Y a [tl]   (prints SAT/UNSAT/TIMEOUT, witness alpha/share)"""
import sys, os, json, time
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE)
from combined import ws, window_from_dirs, exact
import itertools

class LevelEnc(ws.ShareEncoding):
    def __init__(self, window, radius, M, cap, asum):
        self.asum = asum
        super().__init__(window, [None] * (len(window) - 2), radius, M, cap)
    def build_share(self):
        super().build_share()
        X, w = self.var, self.window
        al = []
        for ci in range(1, len(w) - 1):
            c = w[ci]
            used = {(c ^ w[ci - 1]).bit_length() - 1, (c ^ w[ci + 1]).bit_length() - 1}
            al += [-X[c ^ 1 << a ^ 1 << b] for a, b in itertools.combinations(range(9), 2)
                   if a not in used and b not in used]
        self.atmost(al, self.asum, 'alphaSum')

def item(dirs, Y, a, tl=300, M=12):
    w = window_from_dirs(list(dirs))
    cap = Y - 1 - 2 * M * a
    t0 = time.time()
    enc = LevelEnc(w, 4, M, cap, a)
    st, sel, cuts, sec = ws.solve(enc, tl)
    r = dict(dirs=list(dirs), Y=Y, a=a, cap=cap, result=st, seconds=round(time.time() - t0, 1), cuts=cuts)
    if sel:
        A, SH = exact(w, sel, M); r.update(alpha=sum(A), share=sum(SH), W=24 * sum(A) + sum(SH), sel=sel)
    return r

if __name__ == '__main__':
    dirs = json.loads(sys.argv[1]); Y = int(sys.argv[2]); a = int(sys.argv[3])
    tl = float(sys.argv[4]) if len(sys.argv) > 4 else 300
    r = item(dirs, Y, a, tl)
    with open(os.path.join(HERE, 'data', 'levels.jsonl'), 'a') as f: f.write(json.dumps(r) + '\n')
    print(json.dumps(r), flush=True)
