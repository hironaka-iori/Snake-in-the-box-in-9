"""Calibration and positive controls for the integer charge c(x) = sum_Q floor(12/|Q cap S|).

1. Bank statistics: c versus 12 w_3 (loss from h(5) = 2), the census total, the minimum
   internal c and the 1-, 3- and 5-centre window means of c along each snake.
2. Positive controls: for sampled windows of bank snakes and the two adversaries, the W3 CNF
   with cap = true window charge is SAT under the snake's own selection, and with cap = true - 1
   it is UNSAT under that selection (the encoding computes the charge exactly).
usage: controls.py [nsamples]
"""
import json, os, random, sys, itertools
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import w3enc
from pysat.solvers import Cadical153

ROOT = os.path.abspath(os.path.join(HERE, '..', '..', '..'))


def load_sets():
    bank = json.load(open(os.path.join(ROOT, 'work', 'bank9.json')))
    out = [('bank%d' % i, b['vertex_sequence']) for i, b in enumerate(bank)]
    return out


def main():
    ns = int(sys.argv[1]) if len(sys.argv) > 1 else 30
    sets = load_sets()
    res = {}
    allc, loss, minc, mins = [], 0, 10 ** 9, {1: 10 ** 9, 3: 10 ** 9, 5: 10 ** 9}
    tot = []
    for nm, S in sets:
        cs = [w3enc.charge(S, x) for x in S]
        w60 = [w3enc.w3_60(S, x) for x in S]
        tot.append(sum(cs))
        loss += sum(a / 5 - b for a, b in zip(w60, cs))     # 12 w_3 - c >= 0
        inner = cs[1:-1]
        allc += inner
        minc = min(minc, min(inner))
        for k in (1, 3, 5):
            for j in range(len(inner) - k + 1):
                mins[k] = min(mins[k], sum(inner[j:j + k]))
    res['bank'] = dict(snakes=len(sets), mean_internal_c=sum(allc) / len(allc), min_internal_c=minc,
                       min_window_sum={k: v for k, v in mins.items()},
                       census_total_range=[min(tot), max(tot)], census_cap=64512,
                       mean_loss_vs_12w3_per_vertex=loss / sum(len(S) for _, S in sets))
    print(json.dumps(res['bank']), flush=True)
    # positive controls
    rng = random.Random(1)
    ok = bad = 0
    for trial in range(ns):
        nm, S = rng.choice(sets)
        k = rng.choice([1, 3, 5])
        j = rng.randrange(1, len(S) - k - 1)
        win = S[j - 1:j + k + 1]
        # translate so that win[0] = 0
        z = win[0]
        Sz = [x ^ z for x in S]; winz = [x ^ z for x in win]
        true = w3enc.window_charge(winz, Sz)
        for cap, want in ((true, True), (true - 1, False)):
            enc = w3enc.W3Encoding(winz, None, 4, cap)
            Ss = set(Sz)
            assum = [enc.var[v] if v in Ss else -enc.var[v] for v in enc.ball]
            with Cadical153(bootstrap_with=enc.clauses) as s:
                got = s.solve(assumptions=assum)
            if got == want:
                ok += 1
            else:
                bad += 1
                print('CONTROL FAILED', nm, j, k, cap, true, got, flush=True)
    res['controls'] = dict(passed=ok, failed=bad)
    print(json.dumps(res['controls']), flush=True)
    json.dump(res, open(os.path.join(HERE, 'data', 'controls.json'), 'w'), indent=1)


if __name__ == '__main__':
    main()
