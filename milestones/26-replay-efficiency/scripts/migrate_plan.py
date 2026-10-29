"""Projection and order of the packed migration of the Q (237) and R (236) replays (MIGRATION.md).

Reads (never writes) the production replays in work/final_lean (main sources and build files) and
the guarded-build logs of their original build; writes data/migration_plan.json (per window: old
bytes, predicted packed bytes, predicted CPU, staging peak) and data/migration_order.txt (the
order in which `migrate_qr.py` should take the windows).

Model, calibrated on the pilot windows (data/migration_pilot.jsonl):
- packed bytes (.olean + .ilean) = 30 KB + 6.3 KB per segment + 0.185 W B per hint (proof chunks)
  + 0.52 W B per checkpoint tree entry (2^h - 1 entries per checkpoint, one checkpoint every 3
  segments), W the word width, h the tree height (both read from the old main module);
- CPU of the packed module = 1.05 x the wall seconds of the old Check modules in the original
  guarded-build log (pilot: 1.11 and 0.98), at least 0.5 s; regeneration (CaDiCaL portfolio and
  generator) 11 s per million hints and core round (1 round for Q, 2 for R);
- staging peak on disk = 1 MB + 30 B per hint (pilot: 22 and 30 B per hint, during the solver
  portfolio: raw and trimmed LRAT, core CNFs; the source then takes 7 B and the .olean 3.7 B per
  hint).

Order: phase A (the 738 windows whose old checks stayed under 2.9 GB of RSS) before phase B
(the 10 windows that needed 2.9-6.3 GB), each greedy by bytes freed per CPU-second.  Batches:
consecutive windows whose staged files (source 7 B and .olean 3.7 B per hint, plus the largest
solver-phase peak of the batch) fit both --batch-mb and the free disk above --guard-mb at that
point; the free disk starts at --free-mb and grows by what each batch frees once it is swapped.
Writes data/migration_order.tsv (batch, phase, module, hints, bytes freed, CPU seconds).

  python3 migrate_plan.py [--free-mb 450] [--guard-mb 350] [--batch-mb 1024]
"""
import argparse, collections, json, os, re

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.abspath(os.path.join(HERE, '..', '..', '..'))
FINAL = os.path.join(ROOT, 'work', 'final_lean')
LIB = os.path.join(FINAL, '.lake', 'build', 'lib', 'lean')
OUT = os.path.join(HERE, '..', 'data')
LOGS = ['guarded_build_r4b.jsonl', 'guarded_build_r4.jsonl', 'guarded_build_r4_tail.jsonl']


def windows():
    logs = {}
    for f in LOGS:
        for line in open(os.path.join(FINAL, '.lake', f)):
            r = json.loads(line)
            if r['status'] == 'ok' and r['module'].startswith('LocalWindowUnsat.'):
                logs[r['module']] = r
    check_s = collections.Counter()
    peak = collections.defaultdict(float)
    for m, r in logs.items():
        if '.Check' in m:
            w = m.split('.')[1]
            check_s[w] += r['seconds']
            peak[w] = max(peak[w], r['peak_rss_gb'])
    out = []
    for f in sorted(os.listdir(os.path.join(FINAL, 'LocalWindowUnsat'))):
        if not (f.endswith('.lean') and f[0] in 'QR'):
            continue
        w = f[:-5]
        txt = open(os.path.join(FINAL, 'LocalWindowUnsat', f)).read()
        m = re.search(r'(\d+) lemmas, (\d+) hints,\s*(\d+) segments', txt)
        if 'Snake9.ProofPack' in txt or m is None:
            continue   # already packed
        hints, segs = int(m.group(2)), int(m.group(3))
        h = int(re.search(r'\(h := (\d+)\)', txt).group(1))
        ck = re.search(r'open Snake9\.(LratFast2\S*)', txt).group(1)
        W = int(ck[-2:]) if ck[-2:].isdigit() else 13
        files = [os.path.join(FINAL, 'LocalWindowUnsat', f)]
        files += [os.path.join(LIB, 'LocalWindowUnsat', w + e) for e in ('.olean', '.ilean')]
        for d in (os.path.join(FINAL, 'LocalWindowUnsat', w), os.path.join(LIB, 'LocalWindowUnsat', w)):
            if os.path.isdir(d):
                files += [os.path.join(d, g) for g in os.listdir(d)]
        old = sum(os.path.getsize(p) for p in files if os.path.exists(p))
        ncp = (segs - 1) // 3
        new = 30e3 + 6.3e3 * segs + 0.185 * W * hints + 0.52 * W * ncp * (2 ** h - 1)
        rounds = 1 if w[0] == 'Q' else 2
        cpu = max(0.5, 1.05 * check_s[w])
        regen = 11e-6 * hints * rounds + 0.5
        out.append(dict(module=w, hints=hints, segments=segs, h=h, W=W, checkpoints=ncp, old_bytes=old,
                        old_files=len(files), new_bytes=round(new), freed=round(old - new),
                        cpu_s=round(cpu, 1), regen_s=round(regen, 1), old_check_wall_s=round(check_s[w], 1),
                        old_peak_rss_gb=peak[w], staging_peak_bytes=round(1e6 + 30 * hints)))
    return out


def order(ws, free, guard, batch_cap):
    """Phase A then B, greedy by bytes freed per CPU-second; cut into batches (see above)."""
    ratio = lambda w: -w['freed'] / (w['cpu_s'] + w['regen_s'])
    todo = sorted(ws, key=lambda w: (w['old_peak_rss_gb'] > 2.9, ratio(w)))
    avail, t, freed, batches, cum = free - guard, 0.0, 0, [], []
    while todo:
        batch, staged, solver = [], 0, 0
        for w in list(todo):
            if batch and (w['old_peak_rss_gb'] > 2.9) != (batch[0]['old_peak_rss_gb'] > 2.9):
                break
            need = staged + 10.7 * w['hints'] + 1e6 + max(solver, w['staging_peak_bytes'])
            # a window larger than --batch-mb makes a batch of its own once the disk allows it
            if need > (min(batch_cap, avail) if batch else avail):
                if batch:
                    break
                continue   # does not fit yet: try the next window
            batch.append(w)
            todo.remove(w)
            staged += 10.7 * w['hints'] + 1e6
            solver = max(solver, w['staging_peak_bytes'])
        if not batch:
            raise SystemExit('no window fits: %.0f MB usable' % (avail / 1e6))
        for w in batch:
            t += w['cpu_s'] + w['regen_s']
            freed += w['freed']
            cum.append((len(cum) + 1, t, freed))
        batches.append(dict(windows=batch, staging_bytes=round(staged + solver), usable_before=round(avail)))
        avail += sum(w['freed'] for w in batch)
    return batches, cum


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--free-mb', type=float, default=450)
    ap.add_argument('--guard-mb', type=float, default=350)
    ap.add_argument('--batch-mb', type=float, default=1024)
    a = ap.parse_args()
    ws = windows()
    batches, cum = order(ws, a.free_mb * 2**20, a.guard_mb * 2**20, a.batch_mb * 2**20)
    marks = {}
    for target in (5e9, 10e9, 12.5e9, 15e9):
        hit = next((c for c in cum if c[2] >= target), None)
        if hit:
            marks['%.1f GB' % (target / 1e9)] = dict(windows=hit[0], cpu_h=round(hit[1] / 3600, 1))

    def summary(sel):
        return dict(windows=len(sel), hints=sum(w['hints'] for w in sel), old_bytes=sum(w['old_bytes'] for w in sel),
                    new_bytes=sum(w['new_bytes'] for w in sel), freed=sum(w['freed'] for w in sel),
                    cpu_h=round(sum(w['cpu_s'] for w in sel) / 3600, 1),
                    regen_h=round(sum(w['regen_s'] for w in sel) / 3600, 1),
                    old_check_wall_h=round(sum(w['old_check_wall_s'] for w in sel) / 3600, 1))
    tot = summary(ws)
    tot['phase_A'] = summary([w for w in ws if w['old_peak_rss_gb'] <= 2.9])
    tot['phase_B'] = summary([w for w in ws if w['old_peak_rss_gb'] > 2.9])
    tot['phase_B_windows'] = [(w['module'], w['old_peak_rss_gb']) for w in ws if w['old_peak_rss_gb'] > 2.9]
    tot['batches'] = len(batches)
    tot['max_batch_staging_bytes'] = max(b['staging_bytes'] for b in batches)
    tot['first_batches'] = [dict(windows=len(b['windows']), staging_mb=round(b['staging_bytes'] / 2**20),
                                 usable_mb=round(b['usable_before'] / 2**20),
                                 freed_mb=round(sum(w['freed'] for w in b['windows']) / 2**20)) for b in batches[:6]]
    tot['to_free'] = marks
    by = collections.defaultdict(lambda: collections.Counter())
    for w in ws:
        c = by['%s h%d W%d' % (w['module'][0], w['h'], w['W'])]
        for k in ('hints', 'old_bytes', 'new_bytes', 'cpu_s'):
            c[k] += w[k]
        c['n'] += 1
    tot['by_class'] = {k: dict(v) for k, v in sorted(by.items())}
    done = [w for b in batches for w in b['windows']]
    json.dump(dict(model=__doc__.split('Model, ')[1].split('\n\nOrder')[0], totals=tot, windows=done),
              open(os.path.join(OUT, 'migration_plan.json'), 'w'), indent=0)
    with open(os.path.join(OUT, 'migration_order.tsv'), 'w') as f:
        f.write('batch\tphase\tmodule\thints\tfreed_bytes\tcpu_s\n')
        for i, b in enumerate(batches, 1):
            for w in b['windows']:
                f.write('%d\t%s\t%s\t%d\t%d\t%.1f\n' % (i, 'B' if w['old_peak_rss_gb'] > 2.9 else 'A', w['module'],
                                                       w['hints'], w['freed'], w['cpu_s']))
    print(json.dumps(tot, indent=1))


if __name__ == '__main__':
    main()
