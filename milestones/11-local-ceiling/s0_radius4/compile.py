"""Collect window results; build pair specs (proved lower / witness upper) for automaton2."""
import json, sys
from fractions import Fraction as Fr
def sym(s): return 6 if s == '6+' else int(s)
last = {}
for l in open('windows_results.jsonl'):
    r = json.loads(l)
    if r['status'] == 'UNSAT_MODEL':
        print('infeasible window:', r['dirs'], r['alpha_req']); continue
    if r['witness_share'] > 2 * r['M'] * len(r['alphas']) + 1:
        continue   # stale entries of the first (buggy Kmax) run
    last[(tuple(r['dirs']), r['alpha_req'])] = r
# manual entries from runs whose final JSON was lost to the hard timeout (from runB1.log, M=12):
manual = {((0, 1, 2), '2,6+'): (10, 12), ((0, 1, 2), '4,6+'): (0, 11)}
rows = []
for k, r in sorted(last.items()):
    M = r['M']; lo, hi = r['min_lower'], r['witness_share']
    if r['status'] != 'OPT' and k in manual and manual[k][0] > lo:
        lo = manual[k][0]; hi = min(hi, manual[k][1])
    rows.append((k, r['status'], lo, hi, M, r.get('rat_total') or str(sum(Fr(v) for v in r['rat'].values())), r['seconds']))
for k in manual:
    if k not in last:
        rows.append((k, 'TIMEOUT(manual)', manual[k][0], manual[k][1], 12, '?', 560))
pair_lo, pair_hi = {}, {}
for k, st, lo, hi, M, rt, sec in rows:
    print(f'{",".join(map(str,k[0])):8s} alpha={k[1]:9s} {st:10s} shareN in [{lo},{hi}] (M={M}) -> share sum in [{float(Fr(lo,2*M)):.4f},{float(Fr(hi,2*M)):.4f}] witness rational {rt} ({sec}s)')
    if len(k[0]) == 3:
        a, b = map(sym, k[1].split(','))
        pair_lo[f'{a},{b}'] = str(Fr(lo, 2 * M)); pair_hi[f'{a},{b}'] = str(min(Fr(hi, 2 * M), Fr(rt) if rt != '?' else 99))
single_lo = {"1": "4/15", "2": "3/20", "3": "1/24", "4": "0", "5": "0", "6": "0"}
single_hi = {"1": "2/7", "2": "13/84", "3": "1/10", "4": "1/7", "5": "0", "6": "1/14"}
json.dump({'mode': 'pair', 'single': single_lo, 'pair': pair_lo}, open('spec_pair_lo.json', 'w'))
json.dump({'mode': 'pair', 'single': single_hi, 'pair': pair_hi}, open('spec_pair_hi.json', 'w'))
json.dump({'mode': 'single', 'single': single_lo}, open('spec_single_lo.json', 'w'))
json.dump({'mode': 'single', 'single': single_hi}, open('spec_single_hi.json', 'w'))
