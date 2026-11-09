"""Measured replay cost (LRAT hints of the Lean replay) of plain keys and share thresholds.

The pipeline is milestone 25's cost234.replay_cost (the 235 certify pipeline): lazy-cut solve ->
committed CNF; core = original clauses of the trimmed proof of the full CNF (--unsat and default,
fewer hints wins); CaDiCaL portfolio on the core, trimmed, fewest hints wins.  CaDiCaL writes the
proof into a FIFO read by lrattrim (in memory): no proof touches the disk; the CNF is deleted at once.

  plain k6 keys:     cost234.replay_cost(('k6', dirs, syms))
  share thresholds:  the same on wincert_share.from_key(key, M=12, cap=T-1) (RefutedShare W b 12 (T-1))

usage: measure233.py share N [--maxsec S]     (needed-T rows of the 520 plan, spread over solve times)
       measure233.py plain N CLASS            (plan keys of a cost basis class)
Appends to data/replay233.jsonl.
"""
import sys, os, json, time, tempfile, random
import lib233 as L
import cost234 as CO
import wincert_share as ws

CO.TRIM = os.path.join(L.SCR, 'bin', 'lrattrim')
CO.SCR = L.SCR


def guard():
    if L.disk_mb() < 320:
        raise SystemExit('disk below 320 MB: stop')


def replay_share(lk, T, portfolio=CO.PORTFOLIO, seeds=(1, 2), tl=600, solve_tl=300):
    guard()
    wd = tempfile.mkdtemp(dir=L.SCR)
    k = C_rkey(lk)
    enc = ws.from_key(k, M=12, cap=T - 1)
    st, sel, cuts, sec = ws.solve(enc, solve_tl)
    r = dict(kind='share', dirs=list(lk[0]), syms=list(lk[1]), T=T, result=st, solve_s=round(sec, 3), cuts=cuts,
             nv=enc.nv, ncl=len(enc.clauses))
    if st != 'UNSAT':
        os.rmdir(wd)
        return r
    cnf = os.path.join(wd, 'f.cnf'); ccnf = os.path.join(wd, 'c.cnf'); cids = os.path.join(wd, 'core.ids')
    try:
        CO.write(enc.clauses, enc.nv, cnf)
        best = None; t = time.time()
        for a in CO.runs(CO.FULL, seeds[:1]):
            l, h, c = CO.lrat(cnf, len(enc.clauses), a, wd, cids + '.tmp', tl=tl)
            r.setdefault('full', []).append([' '.join(a), h])
            if best is None or h < best[0]:
                best = (h, l, c); os.replace(cids + '.tmp', cids)
        r['full_s'] = round(time.time() - t, 2)
        r['full_hints'], r['core'] = best[0], best[2]
        ids = [int(x) for x in open(cids)]
        kinds = {}
        for i in ids:
            kk = enc.kinds[i - 1].split('@')[0]; kinds[kk] = kinds.get(kk, 0) + 1
        r['core_kinds'] = kinds
        CO.write([enc.clauses[i - 1] for i in ids], enc.nv, ccnf)
        t = time.time(); bh = None
        for a in CO.runs(portfolio, seeds):
            l, h, c = CO.lrat(ccnf, len(ids), a, wd, tl=tl)
            if bh is None or h < bh[0]:
                bh = (h, l, c, ' '.join(a))
        r['core_s'] = round(time.time() - t, 2)
        r['hints'], r['lemmas'], r['core_used'], r['config'] = bh
    finally:
        for f in (cnf, ccnf, cids, cids + '.tmp', os.path.join(wd, 'p.fifo')):
            if os.path.exists(f):
                os.remove(f)
        os.rmdir(wd)
    return r


def C_rkey(lk):
    return L.C.rkey_of(lk)


def replay_plain(lk):
    guard()
    return CO.replay_cost(('k6', tuple(lk[0]), tuple(lk[1])))


def append(r):
    with open(L.REPLAY233, 'a') as f:
        f.write(json.dumps(r) + '\n')


def main():
    import gzip
    mode = sys.argv[1]; n = int(sys.argv[2])
    plan = json.load(gzip.open(os.path.join(L.M28, 'data', 'certplan_520_1.json.gz'), 'rt'))
    done = set()
    if os.path.exists(L.REPLAY233):
        for l in open(L.REPLAY233):
            r = json.loads(l); done.add((r['kind'], tuple(r['dirs']), tuple(r['syms']), r.get('T')))
    random.seed(233)
    if mode == 'share':
        maxsec = float(sys.argv[sys.argv.index('--maxsec') + 1]) if '--maxsec' in sys.argv else 40
        rows = [r for r in plan['share_rows'] if r['seconds'] is not None and r['seconds'] <= maxsec]
        rows.sort(key=lambda r: r['seconds'])
        pick = [rows[int(i * (len(rows) - 1) / max(1, n - 1))] for i in range(n)]
        for r in pick:
            lk = (tuple(r['key'][0]), tuple(r['key'][1]))
            if ('share', lk[0], lk[1], r['T']) in done:
                continue
            t = time.time()
            m = replay_share(lk, r['T'])
            m.update(rec_seconds=r['seconds'], wall=round(time.time() - t, 1))
            append(m)
            print(json.dumps({x: m.get(x) for x in ('T', 'rec_seconds', 'solve_s', 'result', 'full_hints', 'hints',
                                                    'core', 'wall')}), flush=True)
    else:
        cls = sys.argv[3]
        PC = L.PlainCosts()
        keys = []
        for d, al, how, c in plan['plain_keys']:
            lk = L.PR.lumped_of(d, al)
            h, core, b = PC(lk)
            if b.startswith(cls):
                keys.append((lk, h))
        random.shuffle(keys)
        for lk, h in keys[:n]:
            if ('k6', lk[0], lk[1], None) in done:
                continue
            t = time.time()
            m = replay_plain(lk)
            m.update(model=round(h), basis=cls, wall=round(time.time() - t, 1))
            append(m)
            print(json.dumps({x: m.get(x) for x in ('syms', 'model', 'solve_s', 'hints', 'core', 'wall')}), flush=True)


if __name__ == '__main__':
    main()
