"""Proof-size sample: cold CaDiCaL --lrat refutations of static threshold CNFs (alpha units of
wincert + cap T-1), with and without the lex-leader symmetry clauses, trimmed to the empty clause.
Proof files are deleted right after measurement (w3enc.measure_proof).
usage: proof_sample.py N [seed]
"""
import json, os, random, sys, time
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import w3enc
import w3survey as survey
from w3survey import alpha_arg
import refine_w3 as R

OUT = os.path.join(HERE, 'data', 'proof_sample.jsonl')


def main():
    N = int(sys.argv[1]); rng = random.Random(int(sys.argv[2]) if len(sys.argv) > 2 else 0)
    recs = [json.loads(l) for l in open(R.ORACLE)]
    uns = [r for r in recs if r['result'] == 'UNSAT' and len(r['dirs']) == 6]
    pick = rng.sample(uns, min(N, len(uns)))
    singles = [json.loads(l) for l in open(survey.ORACLE)]
    singles = [r for r in singles if r['result'] == 'UNSAT' and len(r['dirs']) == 2 and r.get('T')]
    best = {}
    for r in singles:
        k = tuple(map(tuple, r['alpha']))
        if r['T'] > best.get(k, {'T': 0})['T']:
            best[k] = r
    jobs = [('single', r) for r in best.values()] + [('five', r) for r in pick]
    for kind, r in jobs:
        for sym in (True, False):
            if kind == 'five' and not sym and rng.random() < 0.5:
                continue
            survey.wait_mem()
            st = os.statvfs('/')
            if st.f_bavail * st.f_frsize / 1e6 < 600:
                print('low disk, stop'); return
            w = w3enc.window_from_dirs(r['dirs'])
            enc = w3enc.W3Encoding(w, alpha_arg(r['alpha']), 4, r['T'] - 1, sym=sym)
            # lazy cuts as in the survey (the certificate CNF contains them)
            s, _, cuts, sec = w3enc.solve(enc, 120)
            out = dict(kind=kind, dirs=r['dirs'], alpha=r['alpha'], T=r['T'], sym=sym, status=s, cuts=cuts,
                       solve_s=round(sec, 1))
            if s == 'UNSAT':
                out.update(w3enc.measure_proof(enc, '/tmp/claude-0/-home-user-Snake-in-the-box-in-9/9d4b5ea1-0097-55fa-8dda-100e9a084d22/scratchpad/w3/proof', timeout=600))
            print(json.dumps(out), flush=True)
            with open(OUT, 'a') as f:
                f.write(json.dumps(out) + '\n')


if __name__ == '__main__':
    main()
