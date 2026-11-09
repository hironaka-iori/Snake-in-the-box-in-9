"""Solver calls of milestone 28 (radius 4, the encodings of milestones 10/11/22, unchanged).

  plain(k)          plain feasibility of a lumped window key (wincert / k6loop encoding)
  share_thr(k5, T)  5-centre M12 share threshold: UNSAT means share sum >= T (wincert_share, cap T-1)
  w3_ladder(k6, Ts) 6-centre w_3 charge thresholds on one incremental solver (w3survey.IncW3):
                    UNSAT at T means charge sum >= T
Every call is appended to data/oracle_plain.jsonl, data/oracle_share.jsonl or data/oracle_w3.jsonl
(the record formats of k6loop, refine_share and w3survey respectively).
"""
import os, sys, json, time
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import comb as C
import k6loop
import wincert_share as ws
import w3survey as survey
import w3enc

OPL = os.path.join(HERE, 'data', 'oracle_plain.jsonl')
OSH = os.path.join(HERE, 'data', 'oracle_share.jsonl')
OW3 = os.path.join(HERE, 'data', 'oracle_w3.jsonl')


def _append(path, r):
    if C.disk_mb() < 300:
        raise SystemExit('disk below 300 MB')
    with open(path, 'a') as f:
        f.write(json.dumps(r) + '\n')


def wait_mem():
    while k6loop.mem_gb() < 3.0:
        C.log('low memory, pausing'); time.sleep(60)


def plain(lk, tl=30):
    wait_mem()
    k = C.rkey_of(lk)
    enc = ws.from_key(k)
    st, sel, cuts, sec = ws.solve(enc, tl)
    r = dict(dirs=list(k[0]), alpha=[list(a) for a in k[1]], kind='plain', k=len(k[1]), result=st,
             witness=ws.share_exact(enc, sel, 12) if sel else None, cuts=cuts, seconds=round(sec, 2),
             nv=enc.nv, ncl=len(enc.clauses))
    _append(OPL, r)
    return r


def share_thr(lk, T, tl=60):
    wait_mem()
    k = C.rkey_of(lk)
    t0 = time.time()
    enc = ws.from_key(k, M=12, cap=T - 1)
    build = time.time() - t0
    st, sel, cuts, sec = ws.solve(enc, tl)
    r = dict(dirs=list(k[0]), alpha=[list(a) for a in k[1]], kind='thr', T=T, result=st,
             witness=ws.share_exact(enc, sel, 12) if sel else None, cuts=cuts, seconds=round(sec, 1),
             build=round(build, 1), nv=enc.nv, ncl=len(enc.clauses))
    _append(OSH, r)
    return r


def w3_ladder(lk, Ts, tl=60, cheap=20.0):
    """Ascending thresholds; stops at SAT, TIMEOUT or a slow UNSAT.  Returns [(T, result, s, witness)]."""
    wait_mem()
    k = C.rkey_of(lk)
    ds, al = survey.key(k[0], k[1])
    w = w3enc.window_from_dirs(list(ds)); nc = len(w) - 2
    Ts = [T for T in sorted(Ts) if T - 168 * nc >= 1]
    if not Ts:
        return []
    t0 = time.time()
    enc = survey.IncW3(w, survey.alpha_arg(al), 4, max(Ts) + 1)
    root = enc.root_outputs
    build_s = time.time() - t0
    base = dict(dirs=list(ds), alpha=[list(a) for a in al], kind='m28')
    out = []
    with survey.Cadical153(bootstrap_with=enc.clauses) as sv:
        for T in Ts:
            st, sel, cuts, sec = survey.solve_assume(sv, enc, [-root[T - 168 * nc]], tl)
            wv = w3enc.window_charge(w, sel) if sel else None
            _append(OW3, dict(base, T=T, result=st, witness=wv, seconds=round(sec, 1), cuts=cuts, nv=enc.nv,
                              ncl=len(enc.clauses) + 1, build=round(build_s, 1)))
            out.append((T, st, round(sec, 1), wv))
            if st != 'UNSAT' or sec > cheap:
                break
    return out
