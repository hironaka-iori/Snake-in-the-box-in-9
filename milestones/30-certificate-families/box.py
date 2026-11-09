"""Range ("box") keys: one CNF for a run of sibling keys, against the sum of its members.

A sibling run is a set of paid keys with the same kind and window that agree at every centre
except one, where their symbols form a contiguous run s..t (symbol 6 = counts 6..21).  The box
key has the range (lo(s), hi(t)) at that centre; it is UNSAT iff every member is (the counter
encodes the range exactly), and refuted_narrow (lean/LocalWindowFamilies.lean) gives each
member from it.  Compared: hints of the trimmed proof of the full box CNF (cores.lrat_core,
--seed=1 --unsat) against the sum of the members' full-CNF hints from data/cores.jsonl (same
method).  Output data/box.jsonl.

  nice -n 15 python box.py [--top N] [--minh H]
"""
import sys, os, json, gzip, time, argparse, collections
sys.dont_write_bytecode = True
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import cores as CO   # noqa: E402
k7 = CO.k7
LUMP = k7.LUMP


def runs_of(group):
    """Maximal runs of consecutive symbols among the members (s, idx, hints)."""
    ms = sorted(group)
    out, cur = [], [ms[0]]
    for m in ms[1:]:
        if m[0] == cur[-1][0] + 1:
            cur.append(m)
        else:
            out.append(cur); cur = [m]
    out.append(cur)
    return [r for r in out if len(r) >= 2]


def box_encoding(kind, ds, cs):
    vs = [0]
    for d in ds:
        vs.append(vs[-1] ^ 1 << d)
    return k7.W.Encoding(vs, list(cs) + ([None] if kind == 'H' else []), 4)


def solve(enc, wd):
    cnf = os.path.join(wd, 'b.cnf'); cuts = 0
    try:
        while True:
            CO.write(enc.clauses, enc.nv, cnf)
            st, lem, hints, ids = CO.lrat_core(cnf, len(enc.clauses), wd)
            if st == 'UNSAT':
                return 'UNSAT', hints, len(ids), cuts
            import subprocess
            cads = subprocess.run([CO.CAD, '-q', cnf], capture_output=True, text=True, timeout=600)
            cyc = k7.W.cycles_of(CO.model_sel(enc, cads.stdout))
            if not cyc:
                return 'SAT', None, None, cuts
            for c in cyc:
                enc.add_cycle_cut(c); cuts += 1
    finally:
        if os.path.exists(cnf):
            os.remove(cnf)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--top', type=int, default=40)
    ap.add_argument('--minh', type=float, default=0)
    a = ap.parse_args()
    d = json.load(gzip.open(os.path.join(CO.M25, 'data', 'keys_best234.json.gz'), 'rt'))
    keys = [(k[0], tuple(k[1]), tuple(k[2])) for k in d['keys']]
    full = {}
    for r in CO.records():
        if r.get('hints') is not None:
            full[(r['kind'], tuple(r['dirs']), tuple(r['syms']))] = r['hints']
    sib = json.load(gzip.open(os.path.join(HERE, 'data', 'siblings.json.gz'), 'rt'))
    seeds = {(x[0], tuple(x[1]), tuple(x[2])) for x in
             json.load(gzip.open(os.path.join(HERE, 'data', 'seeds.json.gz'), 'rt'))['full']}
    cands = []
    for g in sib:
        for run in runs_of([tuple(m) for m in g['members']]):
            mk = [keys[i] for _, i, _ in run]
            if not all(k in full and k in seeds for k in mk):
                continue
            tot = sum(full[k] for k in mk)
            if sum(m[2] for m in run) >= a.minh:
                cands.append((sum(m[2] for m in run), g, run, mk))
    cands.sort(key=lambda x: -x[0])
    out = os.path.join(HERE, 'data', 'box.jsonl')
    done = set()
    if os.path.exists(out):
        for l in open(out):
            r = json.loads(l); done.add(json.dumps(r['members']))
    wd = os.path.join(CO.SCR, 'work'); os.makedirs(wd, exist_ok=True)
    n = 0
    with open(out, 'a') as f:
        for tot, g, run, mk in cands:
            tag = json.dumps([[k[0], list(k[1]), list(k[2])] for k in mk])
            if tag in done:
                continue
            if CO.disk_mb() < 300:
                break
            p = g['pos']; s, t = run[0][0], run[-1][0]
            L = lambda x: None if x is None else LUMP[x]   # noqa: E731
            cs = [L(x) for x in g['pre']] + [(LUMP[s][0], LUMP[t][1])] + [L(x) for x in g['post']]
            if g['kind'] == 'H':
                cs = cs[:-1]                     # box_encoding appends the uncounted centre
            t0 = time.time()
            st, h, core, cuts = solve(box_encoding(g['kind'], tuple(g['dirs']), cs), wd)
            rec = dict(kind=g['kind'], dirs=g['dirs'], pos=p, range=[LUMP[s][0], LUMP[t][1]],
                       members=json.loads(tag), member_hints=[full[k] for k in mk], sum=tot,
                       result=st, hints=h, core=core, cuts=cuts, s=round(time.time() - t0, 2))
            f.write(json.dumps(rec, separators=(',', ':')) + '\n'); f.flush()
            print(st, len(mk), tot, h, round(h / tot, 3) if h else None, rec['s'], flush=True)
            n += 1
            if n >= a.top:
                break


if __name__ == '__main__':
    main()
