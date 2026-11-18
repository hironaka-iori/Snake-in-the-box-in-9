"""Encoding / option experiments on level-T share keys (free counts) with the CaDiCaL binary.
usage: expt.py OUT.jsonl 'DIRS' T tl  name=mode,order,step,opt1,opt2...  ...   (run in parallel, 4 at a time)"""
import sys, json
from multiprocessing import Pool
import tier7, binsolve
from enc2 import AltShare
from tier7 import ws, window_from_dirs


def lex(enc, dirs, depth=0):
    """Lex-leader clauses for the transpositions of adjacent coordinates the window does not use (they fix the
    window pointwise): X <=lex X o sigma over the ball vertices in increasing order (first `depth` moved
    vertices, 0 = all).  Auxiliary prefix-equality variables above enc.nv."""
    free = [c for c in range(9) if c not in set(dirs)]
    nv = enc.nv; out = []
    for a, b in zip(free, free[1:]):
        def sg(v):
            x, y = v >> a & 1, v >> b & 1
            return v if x == y else v ^ (1 << a) ^ (1 << b)
        mv = [v for v in sorted(enc.ball) if sg(v) > v]
        if depth:
            mv = mv[:depth]
        e = None
        for v in mv:
            x, y = enc.var[v], enc.var[sg(v)]
            out.append(([-e] if e else []) + [-x, y])
            nv += 1
            out.append(([-e] if e else []) + [x, y, nv]); out.append(([-e] if e else []) + [-x, -y, nv])
            e = nv
    return out


def one(a):
    dirs, T, tl, spec = a
    name, rest = spec.split('=', 1)
    p = rest.split(',')
    mode, order, step, opts = p[0], p[1] == '1', int(p[2]), [x for x in p[3:] if x]
    w = window_from_dirs(list(dirs))
    enc = AltShare(w, ws.alpha_arg([(1, 21)] * 7), 4, 12, T - 1, mode, order, step)
    nc = len(enc.clauses)
    extra = []
    if name.startswith('lex'):
        extra = lex(enc, dirs, int(name[3:] or 0))
    st, sec, cuts, confl = binsolve.solve(enc, opts, tl, extra=extra)
    return dict(dirs=dirs, T=T, name=name, mode=mode, order=order, step=step, opts=opts, vars=enc.nv, clauses=nc,
                result=st, seconds=round(sec, 1), cuts=cuts, conflicts=confl)


if __name__ == '__main__':
    out, dirs, T, tl = sys.argv[1], json.loads(sys.argv[2]), int(sys.argv[3]), float(sys.argv[4])
    with Pool(4) as p:
        for r in p.imap_unordered(one, [(dirs, T, tl, s) for s in sys.argv[5:]]):
            open(out, 'a').write(json.dumps(r) + '\n'); print(r, flush=True)
