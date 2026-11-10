"""Order of the v3 migration (data/order.tsv): greedy by bytes freed per estimated CPU second,
subject to disk: a window is taken only when its staging peak fits the free disk (above the
guard) that the windows before it leave.  Old bytes, hints and old check wall time come from
milestones/26-replay-efficiency/data/migration_plan.json (Q and R).  Model from the pilot
(data/pilot.jsonl): v3 .olean = 30 KB + 2.6 B/hint; CPU = max(0.19 ms/hint, 0.62 x old check
wall); regeneration 12 s per million hints and core round; staging peak 1 MB + 30 B/hint/round.

  python3 order.py [--free-mb 580] [--guard-mb 250] [--skip W ...]
"""
import argparse, json, os
HERE = os.path.dirname(os.path.abspath(__file__))
PLAN = os.path.join(HERE, '..', '..', '26-replay-efficiency', 'data', 'migration_plan.json')
ap = argparse.ArgumentParser()
ap.add_argument('--free-mb', type=float, default=580)
ap.add_argument('--guard-mb', type=float, default=250)
ap.add_argument('--skip', nargs='*', default=[])
a = ap.parse_args()
ws = [w for w in json.load(open(PLAN))['windows'] if w['module'] not in a.skip]
for w in ws:
    r = 2 if w['module'][0] == 'R' else 1
    w['new_est'] = 30000 + 2.6 * w['hints']
    w['freed_est'] = w['old_bytes'] - w['new_est']
    w['cpu_est'] = max(0.19e-3 * w['hints'], 0.62 * w['old_check_wall_s'], 0.5) + 12e-6 * w['hints'] * r
    w['stage_mb'] = 1 + 30 * w['hints'] * r / 2**20
    w['eff'] = w['freed_est'] / w['cpu_est']
ws.sort(key=lambda w: -w['eff'])
free, out, cpu = a.free_mb, [], 0.0
while ws:
    i = next((i for i, w in enumerate(ws) if w['stage_mb'] <= free - a.guard_mb), None)
    if i is None:
        i = min(range(len(ws)), key=lambda i: ws[i]['stage_mb'])
    w = ws.pop(i)
    free += w['freed_est'] / 2**20
    cpu += w['cpu_est']
    out.append((w, free, cpu))
with open(os.path.join(HERE, '..', 'data', 'order.tsv'), 'w') as g:
    g.write('# module\thints\told_bytes\tfreed_est\tcpu_est_s\tstage_mb\tcum_free_mb\tcum_cpu_h\n')
    for w, f, c in out:
        g.write('%s\t%d\t%d\t%d\t%.0f\t%.0f\t%.0f\t%.2f\n' % (w['module'], w['hints'], w['old_bytes'],
                w['freed_est'], w['cpu_est'], w['stage_mb'], f, c / 3600))
