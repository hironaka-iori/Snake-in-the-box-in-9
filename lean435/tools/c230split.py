#!/usr/bin/env python3
"""Run the split route for a share of the 230 plan's split items on ONE machine (milestone 37).

    c230split.py --index S --of N [--parts 8] [--big-parts 16] [--big 35e6] [--jobs 2] [--rss-gb 6.5] [--publish-index 500]

prepare is skipped when the item's sources are already on xfer/c230split/src-N (a relaunch).
Machine S of N takes the items of milestones/37-230-feasibility/data/c230_split_items.txt with
line number % N == S (largest first). For each item that is not yet published on the c230 families:
    splitfarm435.py prepare --parts P   (P = --big-parts above --big plan hints, else --parts)
    splitfarm435.py part --k .. (groups of --jobs parts; parts already on xfer/c230split are skipped)
    splitfarm435.py final --index (publish-index + S) --require-remote
The environment of the c230 workers is required ($PROD435_ADAPTER, $PROD435_CERT, $PROD435_PFX,
$C230_PLAN); this script checks it. A failed item is logged and skipped (re-run the script to retry).
"""
import argparse, os, subprocess, sys, time

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.abspath(os.path.join(HERE, '..', '..'))
LIST = os.path.join(ROOT, 'milestones', '37-230-feasibility', 'data', 'c230_split_items.txt')
sys.path.insert(0, HERE)
sys.dont_write_bytecode = True


def log(msg):
    print(time.strftime('%H:%M:%S ') + msg, flush=True)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--index', type=int, required=True)
    ap.add_argument('--of', type=int, required=True)
    ap.add_argument('--parts', type=int, default=8)
    ap.add_argument('--big-parts', type=int, default=16)
    ap.add_argument('--big', type=float, default=35e6)
    ap.add_argument('--jobs', type=int, default=2, help='parts built at once (one lean each)')
    ap.add_argument('--rss-gb', type=float, default=6.5, help='RssAnon cap per part (pilot peak 3.7 GB at 30.8 M hints)')
    ap.add_argument('--publish-index', type=int, default=500)
    a = ap.parse_args()
    for v in ('PROD435_ADAPTER', 'PROD435_CERT', 'PROD435_PFX', 'C230_PLAN'):
        if not os.environ.get(v):
            raise SystemExit(f'set ${v} (see milestones/37-230-feasibility/PILOT.md)')
    if 'c230' not in os.environ['PROD435_PFX']:
        raise SystemExit('PROD435_PFX is not the c230 family')
    import splitfarm435 as SF
    items = [l.split() for l in open(LIST) if l.strip()]
    mine = [(n, float(e)) for i, (n, e, _r) in enumerate(items) if i % a.of == a.index]
    log(f'machine {a.index} of {a.of}: {len(mine)} split items')
    sf = [sys.executable, os.path.join(HERE, 'splitfarm435.py')]
    plan = os.environ['C230_PLAN']
    for n, est in mine:
        mod = 'LocalWindowCert.' + n
        if SF.published_elsewhere(mod):
            log(f'{n}: already published, skipped')
            continue
        t0 = time.time()
        tips = SF.P.Repo(SF.SPFX).ls()
        steps = []
        if f'src-{n}' in tips:          # sources already pushed (a relaunch): never regenerate them, the
            log(f'{n}: sources on {SF.SPFX}src-{n}, prepare skipped')   # published parts were built on them
            parts = None
        else:
            parts = a.big_parts if est > a.big else a.parts
            steps.append(sf + ['prepare', '--plan', plan, '--name', n, '--parts', str(parts)])
        ok = True
        for cmd in steps:
            if subprocess.run(cmd).returncode != 0:
                log(f'{n}: FAILED at prepare; skipped'); ok = False
        if not ok:
            continue
        if parts is None:               # the part count of the pushed split
            man = SF.fetch_src(n)
            parts = len(man['parts'])
        tips = SF.P.Repo(SF.SPFX).ls()
        todo = [k for k in range(parts) if f'{n}-k{k}' not in tips]
        # `splitfarm435.py part` builds ALL its --k parts at once: give it at most --jobs parts per call
        for i in range(0, len(todo), a.jobs):
            grp = todo[i:i + a.jobs]
            cmd = sf + ['part', '--name', n, '--jobs', str(a.jobs), '--rss-gb', str(a.rss_gb)] + \
                [x for k in grp for x in ('--k', str(k))]
            if subprocess.run(cmd).returncode != 0:
                log(f'{n}: FAILED at part {grp}'); ok = False
                break
        if not ok:
            log(f'{n}: skipped (re-run this script to retry; published parts are kept)')
            continue
        cmd = sf + ['final', '--name', n, '--plan', plan, '--index', str(a.publish_index + a.index), '--require-remote']
        if subprocess.run(cmd).returncode != 0:
            log(f'{n}: FAILED at final; skipped')
            continue
        log(f'{n}: published in {time.time() - t0:.0f} s')


if __name__ == '__main__':
    main()
