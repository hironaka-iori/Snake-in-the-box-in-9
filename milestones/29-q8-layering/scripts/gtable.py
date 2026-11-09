"""Exact tables of g_n(c) (<= c paths), g=_n(c) (exactly c paths) and g3_n(c,t) (exactly c paths,
at most t of them with < 3 vertices), for c = 1.. until g_n(c) = 2^(n-1) (Huang's bound, which no
induced subgraph of max degree 2 can exceed since sqrt(n) > 2 for n >= 5).
usage: python3 gtable.py n [cmax] [timeout_per_query]   -> JSON lines on stdout
"""
import sys, time, json
from gforest import search, check_forest


def maxL(n, c, start, tmax, **kw):
    """largest L with SAT, ascending from a SAT value 'start' (or descending if start is UNSAT)."""
    log = []
    t0 = time.time()
    st, sel, r = search(n, c, start, tmax, **kw)
    log.append((start, st, round(time.time() - t0, 1)))
    if st == 'UNKNOWN':
        return None, None, log
    if st == 'SAT':
        best, wit = len(sel), sel
        L = best + 1
        while True:
            t0 = time.time()
            st, sel, r = search(n, c, L, tmax, **kw)
            log.append((L, st, round(time.time() - t0, 1)))
            if st == 'SAT':
                best, wit = len(sel), sel; L = best + 1
            elif st == 'UNSAT':
                return best, wit, log
            else:
                return ('>=%d' % best), wit, log
    L = start - 1
    while L > 0:
        t0 = time.time()
        st, sel, r = search(n, c, L, tmax, **kw)
        log.append((L, st, round(time.time() - t0, 1)))
        if st == 'SAT':
            return len(sel), sel, log      # len(sel) <= start-1 < UNSAT value
        if st == 'UNKNOWN':
            return ('<%d' % (L + 1)), None, log
        L -= 1
    return 0, None, log


if __name__ == '__main__':
    n = int(sys.argv[1])
    cmax = int(sys.argv[2]) if len(sys.argv) > 2 else 99
    tmax = float(sys.argv[3]) if len(sys.argv) > 3 else 1800
    half = 1 << (n - 1)
    prev = 1
    for c in range(1, cmax + 1):
        rec = {'n': n, 'c': c}
        g, w, log = maxL(n, c, prev, tmax)
        rec['g_le'] = g; rec['log_le'] = log
        if w:
            rec['wit_le'] = w; rec['wit_le_paths'] = check_forest(w, n)
        if isinstance(g, int):
            prev = g
            ge, we, loge = maxL(n, c, g, tmax, cmin=c)
            rec['g_eq'] = ge; rec['log_eq'] = loge
            if isinstance(ge, int):
                for t in (2, 1, 0):
                    g3, w3, log3 = maxL(n, c, ge, tmax, cmin=c, short=t)
                    rec['g3_short%d' % t] = g3; rec['log3_%d' % t] = log3
                    if not isinstance(g3, int):
                        break
        print(json.dumps(rec), flush=True)
        if g == half and n >= 5:
            break
