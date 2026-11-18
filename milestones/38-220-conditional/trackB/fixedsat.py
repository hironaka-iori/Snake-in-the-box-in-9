"""Fixed lumped counts: plain test, then share12 <= T-1 tests (CaDiCaL, lazy cuts), radius 4.
usage: fixedsat.py SHAPE COUNTS "T1,T2,.." tl out   -> records with result and exact witness share"""
import sys, os, json, time
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE)
from combined import ws, window_from_dirs, exact
import wincert
def ranges(cnt): return [c if c < 8 else (8, 21) for c in cnt]
def run(dirs, cnt, Ts, tl, out):
    w = window_from_dirs(list(dirs)); res = []
    enc = wincert.Encoding(w, ranges(cnt), 4)
    st, sel, cuts, sec = ws.solve(enc, tl)
    r = dict(dirs=list(dirs), counts=cnt, T=None, result=st, seconds=round(sec, 1))
    if sel:
        A, SH = exact(w, sel, 12); r.update(share=sum(SH), W=24 * sum(A) + sum(SH), sel=sel)
    res.append(r)
    best = r.get('share')
    if st == 'SAT':
        for T in Ts:
            if best is not None and best < T:
                continue
            enc = ws.ShareEncoding(w, ranges(cnt), 4, 12, T - 1)
            st2, sel2, cuts2, sec2 = ws.solve(enc, tl)
            r2 = dict(dirs=list(dirs), counts=cnt, T=T, result=st2, seconds=round(sec2, 1))
            if sel2:
                A, SH = exact(w, sel2, 12); r2.update(share=sum(SH), W=24 * sum(A) + sum(SH), sel=sel2)
                best = sum(SH)
            res.append(r2)
            if st2 != 'SAT': break
    with open(out, 'a') as f:
        for r in res: f.write(json.dumps(r) + '\n')
    return res
if __name__ == '__main__':
    dirs = json.loads(sys.argv[1]); cnt = json.loads(sys.argv[2]); Ts = [int(x) for x in sys.argv[3].split(',')]
    for r in run(dirs, cnt, Ts, float(sys.argv[4]), sys.argv[5]):
        print(json.dumps({k: v for k, v in r.items() if k != 'sel'}), flush=True)
