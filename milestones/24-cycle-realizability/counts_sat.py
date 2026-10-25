"""Counts along realizable walks: is a long critical walk realizable WITH its counts?

A critical automaton walk prescribes, at each transition, a concrete direction (or only a
shape) and a lumped singleton-square count s of the vertex that becomes internal
(fp.py: LUMP s = (s, s) for s <= 5, (6, 21) for s = 6).  `critical.py` and `lmax.py`
checked the directions only.  Here the counts are imposed jointly, on the WHOLE of Q9:

  variables  X[v] for all 512 vertices (v in the snake);
  clauses    wincert.Encoding with radius 9 (ball = Q9): degree <= 2, at most 2
             endpoints, no 4-cycle, no 6-cycle chord pattern, the window vertices
             selected, alpha(centre) in LUMP[s] at every centre with a prescribed count;
  loop       cycle cuts until the model has no extra cycle component (wincert.decide).

SAT means: a genuine snake of Q9 contains the segment and has exactly those lumped counts at
those vertices, so no local argument of any radius can exclude the segment.

The counts of the walk's transition t (appending direction seq[7 + t]) belong to vertex
vs[7 + t] (fp.windows: the last count is the centre between the last shape direction and
the new one).  The first 6 internal vertices are left free.

Modes:
  concrete W   the whole critical.py walk W (keys235 | allknown) with its own count lift;
  report       for every walk below, (a) the longest SAT prefix with the concrete labels and
               exact counts, (b) the exhaustive label DFS (`dfs`, shape-constrained, first 7
               directions = start shape) with exact counts and with the mean-only condition
               (every prefix sum <= lam (t+1) + R, R = potential range / Q), (c) the minimum
               lumped count sum over long windows of the concrete witness paths (`minsum`).
               Writes data/counts_report.json.

  nice -n 19 python counts_sat.py concrete keys235
  nice -n 19 python counts_sat.py report
"""
import sys, os, json, time
HERE = os.path.dirname(os.path.abspath(__file__))
MS = os.path.abspath(os.path.join(HERE, '..'))
sys.path.insert(0, os.path.join(MS, '10-window-aggregate', 'scripts'))
sys.dont_write_bytecode = True
import wincert as W  # noqa: E402

LUMP = {i: (i, i) for i in range(1, 6)}; LUMP[6] = (6, 21)


def verts(seq):
    vs = [0]
    for d in seq:
        vs.append(vs[-1] ^ 1 << d)
    return vs


def model(seq, counts, first=7, mode='exact', radius=9):
    """Encoding for the path seq with count counts[t] at vertex vs[first + t].
    mode 'exact': alpha in LUMP[s]; 'atmost': alpha <= s (s = 6 -> free)."""
    vs = verts(seq)
    alpha = [None] * (len(vs) - 2)
    for t, s in enumerate(counts):
        i = first + t                     # vertex index, centre index i - 1
        if not 1 <= i <= len(vs) - 2:
            continue
        if mode == 'exact':
            alpha[i - 1] = LUMP[s]
        elif s < 6:
            alpha[i - 1] = (0, s)
    return W.Encoding(vs, alpha, radius)


def check_witness(seq, counts, sel, first=7):
    """Independent re-check of a SAT witness: induced path through vs, alpha values."""
    S = set(sel)
    vs = verts(seq)
    assert all(v in S for v in vs)
    for v in S:
        deg = sum((v ^ 1 << k) in S for k in range(9))
        assert 1 <= deg <= 2
    assert sum(sum((v ^ 1 << k) in S for k in range(9)) == 1 for v in S) == 2
    # connected (a single path) and induced: |E| = |V| - 1
    E = sum(sum((v ^ 1 << k) in S for k in range(9)) for v in S) // 2
    assert E == len(S) - 1
    st, seen = [vs[0]], set()
    while st:
        v = st.pop()
        if v in seen:
            continue
        seen.add(v); st.extend(v ^ 1 << k for k in range(9) if (v ^ 1 << k) in S)
    assert seen == S
    al = []
    for t, s in enumerate(counts):
        i = first + t
        if not 1 <= i <= len(vs) - 2:
            continue
        c = vs[i]
        used = {(c ^ vs[i - 1]).bit_length() - 1, (c ^ vs[i + 1]).bit_length() - 1}
        a = sum((c ^ 1 << x ^ 1 << y) not in S for x in range(9) for y in range(x + 1, 9)
                if x not in used and y not in used)
        lo, hi = LUMP[s]
        assert lo <= a <= hi, (i, a, s)
        al.append(a)
    return len(S) - 1, al


def run(seq, counts, first=7, mode='exact', certify=False):
    t0 = time.time()
    enc = model(seq, counts, first, mode)
    st, x, cuts = W.decide(enc, certify=certify)
    out = dict(status=st, cuts=cuts, seconds=round(time.time() - t0, 1),
               variables=enc.nv, clauses=len(enc.clauses))
    if st == 'SAT':
        out['snake_edges'], out['alpha'] = check_witness(seq, counts, x, first) if mode == 'exact' else (len(x) - 1, None)
        out['snake'] = sorted(x)
    elif st == 'UNSAT' and certify:
        out['proof'] = x
    return out


def corners_absent(enc, vs, i):
    c = vs[i]
    used = {(c ^ vs[i - 1]).bit_length() - 1, (c ^ vs[i + 1]).bit_length() - 1}
    return [-enc.var[c ^ 1 << a ^ 1 << b] for a in range(9) for b in range(a + 1, 9)
            if a not in used and b not in used]


def minsum(seq, idx, hi=None, time_cap=600, radius=9):
    """min over snakes of Q9 containing the path seq of sum_{i in idx} min(alpha(vs[i]), 6).
    Unary per-centre totalizers (outputs >= 1..6), one global totalizer; descending bound
    with assumptions; cycle cuts as in wincert.decide.  Returns (min, witness, info);
    min = None if the path alone is UNSAT."""
    from pysat.card import ITotalizer
    from pysat.solvers import Cadical153
    vs = verts(seq)
    enc = W.Encoding(vs, [None] * (len(vs) - 2), radius)
    top = enc.nv
    ys, extra = [], []
    for i in idx:
        t = ITotalizer(corners_absent(enc, vs, i), ubound=6, top_id=top)
        top = t.top_id; extra += t.cnf.clauses; ys += t.rhs[:6]
    if hi is None:
        hi = 6 * len(idx)
    g = ITotalizer(ys, ubound=min(hi + 1, len(ys)), top_id=top)
    top = g.top_id; extra += g.cnf.clauses
    t0 = time.time()
    best, wit, cuts, calls = None, None, 0, 0
    with Cadical153(bootstrap_with=enc.clauses + extra) as s:
        bound = hi                       # look for sum <= bound
        while bound >= 0 and time.time() - t0 < time_cap:
            assum = [-g.rhs[bound]] if bound < len(g.rhs) else []
            calls += 1
            if not s.solve(assumptions=assum):
                break
            m = s.get_model()
            sel = [v for v in enc.ball if m[enc.var[v] - 1] > 0]
            cyc = W.cycles_of(sel)
            if cyc:
                for c in cyc:
                    s.add_clause([-enc.var[w] for w in c]); cuts += 1
                continue
            val = 0
            for i in idx:
                val += min(6, sum(m[-l - 1] < 0 for l in corners_absent(enc, vs, i)))
            best, wit = val, sel
            bound = val - 1
        done = time.time() - t0 < time_cap
    return best, wit, dict(cuts=cuts, calls=calls, seconds=round(time.time() - t0, 1), optimal=done)


def lumped_alpha(sel, seq, i):
    S = set(sel); vs = verts(seq); c = vs[i]
    used = {(c ^ vs[i - 1]).bit_length() - 1, (c ^ vs[i + 1]).bit_length() - 1}
    return min(6, sum((c ^ 1 << a ^ 1 << b) not in S for a in range(9) for b in range(a + 1, 9)
                      if a not in used and b not in used))


def feasible_sum(seq, idx, target, radius=9):
    """Is there a snake of Q9 containing the path seq with sum_{i in idx} min(alpha, 6) <= target?"""
    from pysat.card import ITotalizer
    from pysat.solvers import Cadical153
    vs = verts(seq)
    enc = W.Encoding(vs, [None] * (len(vs) - 2), radius)
    top, ys, extra = enc.nv, [], []
    for i in idx:
        t = ITotalizer(corners_absent(enc, vs, i), ubound=6, top_id=top)
        top = t.top_id; extra += t.cnf.clauses; ys += t.rhs[:6]
    if target >= len(ys):
        assum = []
    else:
        if target < 0:
            return False
        g = ITotalizer(ys, ubound=target + 1, top_id=top)
        extra += g.cnf.clauses; assum = [-g.rhs[target]]
    with Cadical153(bootstrap_with=enc.clauses + extra) as s:
        while s.solve(assumptions=assum):
            m = s.get_model()
            sel = [v for v in enc.ball if m[enc.var[v] - 1] > 0]
            cyc = W.cycles_of(sel)
            if not cyc:
                return sel
            for c in cyc:
                s.add_clause([-enc.var[w] for w in c])
    return False


def feasible_exact(seq, counts, first=7):
    enc = model(seq, counts, first, 'exact')
    st, x, _ = W.decide(enc, certify=False)
    return x if st == 'SAT' else False


def induced_ok(vs, inpath, nv):
    last = vs[-1]
    return nv not in inpath and not any((nv ^ 1 << k) in inpath and (nv ^ 1 << k) != last for k in range(9))


def dfs(states, counts, mode, lam=4, R=0, time_cap=1800, node_cap=10 ** 6):
    """Exhaustive DFS over the concrete labels of the shape walk states[0..n] (first 7
    directions = states[0] w.l.o.g.; unused labels interchangeable), pruned by the counts
    model on every prefix.  mode 'exact': alpha(vs[7 + j]) in LUMP[counts[j]];
    mode 'sum': every prefix sum_{j <= t} min(alpha(vs[7 + j]), 6) <= lam (t + 1) + R.
    Returns dict(longest=L, witness, nodes, sat_calls, exhaustive)."""
    from shapes import canon
    n = len(counts)
    seq = list(states[0])
    vs = verts(seq)
    assert len(set(vs)) == len(vs)
    inpath = set(vs)
    st = dict(best=0, wit=list(seq), nodes=0, calls=0, t0=time.time(), stop=False)

    def ok(seq, t):
        st['calls'] += 1
        if mode == 'exact':
            return feasible_exact(seq, counts[:t + 1])
        return feasible_sum(seq, list(range(7, 8 + t)), int(lam * (t + 1) + R))

    def go(t):
        st['nodes'] += 1
        if t > st['best']:
            st['best'] = t; st['wit'] = list(seq)
        if t == n:
            st['stop'] = True; return
        if st['nodes'] > node_cap or time.time() - st['t0'] > time_cap:
            st['stop'] = 'cap'; return
        tail = seq[-6:]
        cand = [d for d in range(9) if canon(tail + [d]) == tuple(states[t + 1])]
        new = [d for d in cand if d not in seq]
        cand = [d for d in cand if d in seq] + new[:1]
        for d in cand:
            nv = vs[-1] ^ 1 << d
            if not induced_ok(vs, inpath, nv):
                continue
            seq.append(d); vs.append(nv); inpath.add(nv)
            # vertex vs[7 + t] has become internal: it carries counts[t]
            if ok(seq, t):
                go(t + 1)
            seq.pop(); vs.pop(); inpath.discard(nv)
            if st['stop']:
                return

    sys.setrecursionlimit(20000)
    go(0)
    return dict(longest=st['best'], witness=st['wit'], nodes=st['nodes'], sat_calls=st['calls'],
                exhaustive=st['stop'] != 'cap',
                complete_walk=st['best'] == n, seconds=round(time.time() - st['t0']))


def feasible_sum_fast(seq, idx, target, radius=4):
    """Relaxed (sound for UNSAT) check: radius-`radius` ball around the counted centres,
    no cycle cuts.  Returns True/False."""
    from pysat.card import ITotalizer
    from pysat.solvers import Cadical153
    vs = verts(seq)
    cen = [vs[i] for i in idx]
    enc = W.Encoding([vs[0]] + cen + [vs[idx[-1] + 1]], [None] * len(cen), radius)
    for v in vs:                                   # the whole prefix path is selected
        if v in enc.var:
            enc.add([enc.var[v]], 'path')
    for i in range(len(vs)):                       # induced: other neighbours of path vertices absent
        for k in range(9):
            w = vs[i] ^ 1 << k
            if w in enc.var and w not in vs:
                if 0 < i < len(vs) - 1:
                    enc.add([-enc.var[w]], 'induced')
    top, ys, extra = enc.nv, [], []
    for i in idx:
        t = ITotalizer(corners_absent(enc, vs, i), ubound=6, top_id=top)
        top = t.top_id; extra += t.cnf.clauses; ys += t.rhs[:6]
    if target < 0:
        return False
    assum = []
    if target < len(ys):
        g = ITotalizer(ys, ubound=target + 1, top_id=top)
        extra += g.cnf.clauses; assum = [-g.rhs[target]]
    with Cadical153(bootstrap_with=enc.clauses + extra) as s:
        return s.solve(assumptions=assum)


def allpaths(lam, R=0, radius=4, max_depth=40, level_cap=20000, time_cap=3600, log=None):
    """Level-by-level search over ALL induced direction sequences (first label 0, a new label
    is the smallest unused one), keeping a node of t centres vs[1..t] only if some snake has
    every prefix sum_{i <= j} min(alpha(vs[i]), 6) <= lam j + R (checked at each level for the
    current prefix).  Returns the level profile."""
    t0 = time.time()
    level = [[0]]
    prof = []
    for t in range(1, max_depth + 1):
        nxt, unsat, calls = [], 0, 0
        for seq in level:
            vs = verts(seq)
            used = set(seq)
            cand = [d for d in sorted(used) if d != seq[-1]]
            if len(used) < 9:
                cand.append(len(used))
            S = set(vs)
            for d in cand:
                nv = vs[-1] ^ 1 << d
                if nv in S or any((nv ^ 1 << k) in S and (nv ^ 1 << k) != vs[-1] for k in range(9)):
                    continue
                s2 = seq + [d]
                calls += 1
                if feasible_sum_fast(s2, list(range(1, t + 1)), int(lam * t + R), radius):
                    nxt.append(s2)
                else:
                    unsat += 1
            if time.time() - t0 > time_cap:
                break
        rec = dict(depth=t, survivors=len(nxt), unsat_leaves=unsat, sat_calls=calls,
                   seconds=round(time.time() - t0), complete=time.time() - t0 <= time_cap)
        prof.append(rec)
        if log:
            print(json.dumps(rec), flush=True)
        level = nxt
        if not level or len(level) > level_cap or not rec['complete']:
            break
    return prof, level[:5]


def walk(which):
    d = json.load(open(os.path.join(HERE, 'data', f'critical_walk_{which}.json')))
    return d['directions'], d['new_counts']


def cyc_walk(shapes, counts, phase, n):
    p = len(counts)
    sh = shapes * (p // len(shapes)) if len(shapes) < p else shapes
    st = [tuple(int(c) for c in sh[(phase + t) % p]) for t in range(n + 1)]
    return st, [counts[(phase + t) % p] for t in range(n)]


def report(cap=150):
    from fractions import Fraction as Fr
    from shapes import canon
    A = json.load(open(os.path.join(HERE, 'data', 'cutloop_allknown_opt.json')))['rounds']
    K = json.load(open(os.path.join(HERE, 'data', 'cutloop_keys235_opt.json')))['rounds']
    jobs = []
    for which, lam, R in (('keys235', Fr(4), Fr(5)), ('allknown', Fr(65, 16), Fr(75, 16))):
        seq, cnt = walk(which)
        jobs.append((f'critical_walk_{which}', [canon(seq[t:t + 7]) for t in range(len(seq) - 6)],
                     cnt, lam, R, seq))
    for name, r, lam, R in (('allknown_16cycle', A[0], Fr(65, 16), Fr(75, 16)),
                            ('allknown_80cycle', A[1], Fr(65, 16), Fr(75, 16)),
                            ('keys235_4cycle_0123456', K[0], Fr(4), Fr(5))):
        st, c = cyc_walk(r['shapes'], r['counts'], 0, 160)
        jobs.append((name, st, c, lam, R, None))
    out = {}
    for name, st, c, lam, R, seq in jobs:
        rec = dict(transitions=len(c), count_mean=sum(c) / len(c), lam=str(lam), R=str(R))
        if seq is not None:                      # concrete labels, exact counts: longest SAT prefix
            n = 0
            while n < len(c) and run(seq[:8 + n], c[:n + 1])['status'] == 'SAT':
                n += 1
            rec['concrete_exact_longest'] = n
            mins = {}
            for L in (6, 10, 20, 40, len(seq) - 8):
                b, _, inf = minsum(seq[:8 + L], list(range(7, 7 + L)), time_cap=cap)
                mins[L] = dict(min_sum=b, mean=b / L, walk_sum=sum(c[:L]), optimal=inf['optimal'])
            rec['concrete_min_lumped_sum'] = mins
        for mode in ('exact', 'sum'):
            r = dfs(st, c, mode, lam=lam, R=R, time_cap=cap)
            rec[f'dfs_{mode}'] = {k: v for k, v in r.items() if k != 'witness'}
        print(name, json.dumps(rec), flush=True)
        out[name] = rec
    json.dump(out, open(os.path.join(HERE, 'data', 'counts_report.json'), 'w'), indent=1)


def main():
    what = sys.argv[1]
    if what == 'report':
        return report()
    which = sys.argv[2]
    seq, counts = walk(which)
    res = {}
    if what == 'concrete':
        r = run(seq, counts)
        print(which, {k: v for k, v in r.items() if k != 'snake'}, flush=True)
        res = dict(which=which, path_edges=len(seq), transitions=len(counts),
                   count_sum=sum(counts), result=r)
        json.dump(res, open(os.path.join(HERE, 'data', f'counts_concrete_{which}.json'), 'w'))


if __name__ == '__main__':
    main()
