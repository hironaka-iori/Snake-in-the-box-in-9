"""Summary of the w_3 survey: solver-call counts, proof-size statistics, cost estimate.
Writes data/summary.json.  usage: summarize.py"""
import json, os, statistics as st
HERE = os.path.dirname(os.path.abspath(__file__))
D = os.path.join(HERE, 'data')


def main():
    A = [json.loads(l) for l in open(os.path.join(D, 'w3_alpha_oracle.jsonl'))]
    P = [json.loads(l) for l in open(os.path.join(D, 'w3_oracle.jsonl'))]
    out = {}
    calls = {}
    for r in A:
        c = len(r['dirs']) - 1
        k = f"{c}-centre {r.get('kind', 'thr')}"
        d = calls.setdefault(k, {})
        d[r['result']] = d.get(r['result'], 0) + 1
    out['alpha_conditioned_calls'] = calls
    out['direction_only_calls'] = len(P)
    keys5 = {(tuple(r['dirs']), json.dumps(r['alpha'])) for r in A if len(r['dirs']) == 6}
    out['five_centre_keys_tested'] = len(keys5)
    hints = [r['proof']['lrat_hints'] for r in A if r.get('proof') and 'lrat_hints' in r['proof']]
    failed = [r for r in A if r.get('proof') and 'lrat_hints' not in r['proof']]
    if hints:
        hs = sorted(hints)
        out['proofs_in_loop'] = dict(n=len(hints), failed_over_cap=len(failed), median=st.median(hs),
                                     mean=st.mean(hs), p90=hs[int(0.9 * len(hs))], max=hs[-1], total=sum(hs))
    ps = os.path.join(D, 'proof_sample.jsonl')
    if os.path.exists(ps):
        S = [json.loads(l) for l in open(ps)]
        out['proof_sample'] = [{k: r.get(k) for k in ('kind', 'dirs', 'alpha', 'T', 'sym', 'status', 'solve_s',
                                                     'lrat_hints', 'core_clauses', 'failed')} for r in S]
    rate = 34.0 / 289e6            # kernel-hours per hint (237 replay)
    if hints:
        out['cost_per_certificate_kernel_h'] = dict(median=out['proofs_in_loop']['median'] * rate,
                                                    mean=out['proofs_in_loop']['mean'] * rate)
        for N in (1000, 5000, 11425):
            out[f'cost_{N}_certificates_kernel_h_at_mean'] = N * out['proofs_in_loop']['mean'] * rate
    ev = os.path.join(D, 'w3_eval.json')
    if os.path.exists(ev):
        e = json.load(open(ev))
        out['eval'] = {k: ({kk: vv for kk, vv in v.items() if kk != 'cycle'} if isinstance(v, dict) else v)
                       for k, v in e.items()}
    json.dump(out, open(os.path.join(D, 'summary.json'), 'w'), indent=1)
    print(json.dumps(out, indent=1))


if __name__ == '__main__':
    main()
