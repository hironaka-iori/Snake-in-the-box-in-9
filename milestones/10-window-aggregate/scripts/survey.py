"""Exhaustive local-window feasibility survey (solver evidence, not proofs).

For every canonical window shape with k centers and every alpha tuple with
entries 1..K, decide the radius-r local ball model of wincert.py with
CaDiCaL and lazy cycle cuts.  SAT answers are explicit acyclic local
configurations; UNSAT answers are uncertified unless replayed by certify.py.

  python survey.py --centers 3 --radius 3 --kmax 6 --out ../data/survey_c3_r3.json
  python survey.py --centers 4 --radius 3 --quads ../data/relevant_quads.json --out ../data/survey_c4_r3.json
"""
import argparse, itertools, json, time
from multiprocessing import Pool
from wincert import Encoding, decide, window_from_dirs


def canon(ds):
    m, r = {}, []
    for d in ds:
        m.setdefault(d, len(m)); r.append(m[d])
    return tuple(r)


def shapes(ncent):
    """Direction sequences of induced windows, up to relabelling and reversal."""
    out = set()
    for ds in itertools.product(range(ncent + 1), repeat=ncent + 1):
        ds = canon(ds); vs = window_from_dirs(ds)
        ok = len(set(vs)) == len(vs) and all((vs[i] ^ vs[j]).bit_count() != 1
                                               for i in range(len(vs)) for j in range(i + 2, len(vs)))
        if ok:
            out.add(min(ds, canon(ds[::-1])))
    return sorted(out)


def job(arg):
    ds, al, radius = arg
    t = time.time()
    st, sel, cuts = decide(Encoding(window_from_dirs(ds), list(al), radius), certify=False)
    return {'directions': list(ds), 'alpha': list(al), 'status': st, 'cycle_cuts': cuts,
            'seconds': round(time.time() - t, 2), 'selection': sel if st == 'SAT' else None}


if __name__ == '__main__':
    ap = argparse.ArgumentParser()
    ap.add_argument('--centers', type=int, required=True)
    ap.add_argument('--radius', type=int, default=3)
    ap.add_argument('--kmax', type=int, default=6)
    ap.add_argument('--quads', help='JSON list of alpha tuples to test instead of all tuples')
    ap.add_argument('--workers', type=int, default=4)
    ap.add_argument('--out', required=True)
    a = ap.parse_args()
    tuples = ([tuple(t) for t in json.load(open(a.quads))] if a.quads else
              list(itertools.product(range(1, a.kmax + 1), repeat=a.centers)))
    jobs = [(ds, t, a.radius) for ds in shapes(a.centers) for t in tuples]
    with Pool(a.workers) as p:
        res = list(p.imap(job, jobs))
    json.dump({'centers': a.centers, 'radius': a.radius, 'endpoint_budget': 2,
               'scope': 'Local ball model; UNSAT is solver evidence unless certified.',
               'results': res}, open(a.out, 'w'))
    print(sum(r['status'] == 'UNSAT' for r in res), 'UNSAT of', len(res))
