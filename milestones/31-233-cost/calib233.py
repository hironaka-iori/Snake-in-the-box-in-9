"""Calibration of the cost models from this milestone's measured replays (data/replay233.jsonl).

share: hints = A * t^B (least squares in log-log on the samples with t >= 0.05 s), t = the solve time
       of the threshold at the level that is certified (floor F hints); also the ratio to the old
       milestone-28 model (1 M hints per solver-second of the call that proved the level or more).
plain: m28_sec_scale = the factor on milestone 28's own solve times (wincert_share-encoded plain
       solves) that makes the bin model of milestone 25 (model234.json) match the measured hints in
       aggregate (1.0 if fewer than 8 samples).
Writes data/calib233.json.
"""
import json, math, os
import numpy as np
import lib233 as L


def main():
    rs = [json.loads(l) for l in open(L.REPLAY233)]
    sh = [r for r in rs if r['kind'] == 'share' and r.get('hints')]
    x = np.array([math.log(r['solve_s']) for r in sh if r['solve_s'] >= 0.05])
    y = np.array([math.log(r['hints']) for r in sh if r['solve_s'] >= 0.05])
    B, lnA = np.polyfit(x, y, 1)
    A = math.exp(lnA)
    pred = [max(1.2e4, A * max(r['solve_s'], 1e-3) ** B) for r in sh]
    meas = [r['hints'] for r in sh]
    old = [max(1.2e4, 1e6 * r['rec_seconds']) for r in sh]
    share = dict(A=A, B=float(B), floor=float(min(meas)), n=len(sh),
                 pred_over_meas=sum(pred) / sum(meas), old_over_meas=sum(old) / sum(meas),
                 hints_per_solve_second=sum(meas) / sum(r['solve_s'] for r in sh),
                 full_over_core_portfolio=sum(r['full_hints'] for r in sh) / sum(meas))
    pl = [r for r in rs if r['kind'] == 'k6' and r.get('hints') is not None and r.get('model')]
    scale = 1.0
    if len(pl) >= 8:
        PC = L.PlainCosts()
        PC.me = {}
        m28 = PC.m28

        def tot(sc):
            PC.scale = sc
            return sum(PC(L.lk_of(r['dirs'], r['syms']))[0] for r in pl)
        target = sum(r['hints'] for r in pl)
        lo, hi = 0.01, 10.0
        for _ in range(40):
            mid = math.sqrt(lo * hi)
            if tot(mid) > target:
                hi = mid
            else:
                lo = mid
        scale = math.sqrt(lo * hi)
    out = dict(share=share, m28_sec_scale=scale, plain_samples=len(pl),
               plain_measured=sum(r['hints'] for r in pl), plain_model_before=sum(r['model'] for r in pl))
    json.dump(out, open(L.CALIB, 'w'), indent=1)
    print(json.dumps(out, indent=1))


if __name__ == '__main__':
    main()
