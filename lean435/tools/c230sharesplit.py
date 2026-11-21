#!/usr/bin/env python3
"""Share certificates of the 230 plan by the split route (milestone 37), for the items whose monolithic
Lean build takes hours and keeps being lost to container restarts.

    c230sharesplit.py own  NAME [--parts 16] [--index 690]   prepare (once), every unpublished part 2 at a
                                                             time, then the final (published to
                                                             xfer/c230help/w<index>); rerunnable
    c230sharesplit.py help [--hours 12] [--rss-gb 6.5] [--first W01234501:14 ...]
                                                             helper: build unpublished parts of the items in
                                                             ITEMS (sources published, part not yet), one
                                                             part at a time, until none is left; a part that
                                                             fails here (e.g. above --rss-gb) is skipped by this
                                                             process from then on. Parts above 6.5 GB: one
                                                             helper alone on a 16 GB machine with --rss-gb 12
                                                             and --first <those parts>

Each part is a separate module, published to xfer/c230split/NAME-k<K> as soon as it is built, so a
restart loses at most the parts in progress. There are no claims: a helper takes the parts in a random
order and re-checks the remote before each one; a duplicate part is harmless (the final checks every
part's base .olean hashes). The c230 environment is set here (PROD435_ADAPTER, PROD435_CERT, PROD435_PFX).
"""
import argparse, os, random, subprocess, sys, time

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.abspath(os.path.join(HERE, '..', '..'))
os.environ.setdefault('PROD435_ADAPTER', os.path.join(HERE, 'c230.py'))
os.environ.setdefault('PROD435_CERT', os.path.join(HERE, 'c230.py') + ' cert')
os.environ['PROD435_PFX'] = os.environ.get('PROD435_PFX', 'refs/heads/xfer/c230/')
sys.path.insert(0, HERE)
sys.dont_write_bytecode = True
import prod435 as P  # noqa: E402
import splitfarm435 as S  # noqa: E402

PLAN = os.path.join(ROOT, 'milestones', '37-230-feasibility', 'data', 'c230share.json.gz')
ITEMS = ['W01234501AFFFFFFFK29', 'W01234560AFFFFFFFK29', 'W01234561AFFFFFFFK29', 'W01234564AFFFFFFFK29',
         'W01234567AFFFFFFFK29']
SF = [sys.executable, os.path.join(HERE, 'splitfarm435.py')]


def log(m):
    print(time.strftime('%H:%M:%S ', time.gmtime()) + m, flush=True)


def tips():
    return S.P.Repo(S.SPFX).ls()


def nparts(name):
    lk = S.base_lock(name)
    try:
        return sorted(int(p[0].rsplit('.K', 1)[1]) for p in S.fetch_src(name)['parts'])
    finally:
        lk.close()


def run(cmd):
    log(' '.join(cmd[2:]))
    return subprocess.run(cmd).returncode


def cmd_own(a):
    n = a.name
    if f'src-{n}' not in tips():
        if run(SF + ['prepare', '--plan', PLAN, '--name', n, '--parts', str(a.parts), '--jobs', '3']):
            sys.exit('prepare failed')
    ks = nparts(n)
    for i in range(0, len(ks), 2):
        t = tips()
        todo = [k for k in ks[i:i + 2] if f'{n}-k{k}' not in t]
        if todo and run(SF + ['part', '--name', n, '--jobs', '2', '--rss-gb', str(a.rss_gb)]
                        + [x for k in todo for x in ('--k', str(k))]):
            log(f'part {todo} FAILED')
    t = tips()
    miss = [k for k in ks if f'{n}-k{k}' not in t]
    if miss:
        sys.exit(f'{n}: parts {miss} not published (rerun)')
    sys.exit(run(SF + ['final', '--name', n, '--plan', PLAN, '--index', str(a.index), '--require-remote']))


def cmd_help(a):
    end = time.time() + a.hours * 3600
    failed = set()       # parts that failed here (e.g. above --rss-gb): left to a --rss-gb 12 helper
    while time.time() < end:
        t = tips()
        cand = []
        for n in ITEMS:
            if f'src-{n}' not in t:
                continue
            for k in nparts(n):
                if f'{n}-k{k}' not in t and (n, k) not in failed:
                    cand.append((n, k))
        if not cand:
            log('no unpublished part of a share split item with published sources: done'
                + (f' ({len(failed)} failed here: {sorted(failed)})' if failed else ''))
            return
        first = [c for c in cand if f'{c[0][:9]}:{c[1]}' in a.first]
        n, k = first[0] if first else random.choice(cand)
        if run(SF + ['part', '--name', n, '--jobs', '1', '--rss-gb', str(a.rss_gb), '--k', str(k)]):
            log(f'{n} part {k} FAILED (skipped from now on in this process)')
            failed.add((n, k))
            time.sleep(60)


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    sub = ap.add_subparsers(dest='cmd', required=True)
    p = sub.add_parser('own')
    p.add_argument('name')
    p.add_argument('--parts', type=int, default=16)
    p.add_argument('--index', type=int, default=690)
    p.add_argument('--rss-gb', type=float, default=6.5)
    p = sub.add_parser('help')
    p.add_argument('--hours', type=float, default=12)
    p.add_argument('--rss-gb', type=float, default=6.5)
    p.add_argument('--first', nargs='*', default=[], help='parts to take first, e.g. W01234501:14 (big parts)')
    a = ap.parse_args()
    {'own': cmd_own, 'help': cmd_help}[a.cmd](a)


if __name__ == '__main__':
    main()
