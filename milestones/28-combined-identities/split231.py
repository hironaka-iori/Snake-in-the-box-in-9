#!/usr/bin/env python3
"""Solver tests that split the expensive tail of the 231 certificate plan (milestone 28,
"Certificate plan for 231"), on several machines.

Input: a job file written by `certplan231.py full` (data/split231_jobs*.jsonl.gz), one JSON per line:
  {"kind": "c", "key": [ctx, dirs, t], "T": level, "tl": seconds}   ctx-7/ctx-8 share threshold
  {"kind": "p", "key": [dirs, lumped syms], "tl": seconds}          plain window
Each job runs exactly as the farm runs it (share7.thr for thresholds, solvers.plain for plain
windows: the same encodings and record formats).  Worker I of W runs the jobs with
int(sha1(json key).hexdigest(), 16) % W == I, in file order (the file is sorted by priority), and
appends the records to data/split231/{ctx,plain}_w<I>.jsonl; they are published every
--publish-min minutes to refs/heads/xfer/231x/w<I> (farm231.py's transfer code: temporary bare
repositories, fast-forward only, never forced, never deleted).  A restarted worker merges its branch
first and skips jobs already done.

  nice -n 10 python3 split231.py run --index I --workers W --hours H [--procs 4] [--jobs FILE]
  python3 split231.py status
  python3 split231.py merge        # all branches -> data/ctxshare_s231.jsonl.gz, data/oracle_plain_s231.jsonl.gz

Setup: the farm231.py worker setup (same sparse checkout, numpy, python-sat), plus this file and the
job file.
"""
import argparse, gzip, hashlib, json, os, sys, time
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import farm231 as F                      # noqa: E402  (transfer helpers; hooks the record loaders)
import share7 as S7                      # noqa: E402
import solvers as SV                     # noqa: E402
import comb as C                         # noqa: E402

F.PFX = 'refs/heads/xfer/231x/'
OUTD = os.path.join(HERE, 'data', 'split231')
JOBS = os.path.join(HERE, 'data', 'split231_jobs.jsonl.gz')


def jkey(j):
    return json.dumps([j['kind'], j['key'], j.get('T')], separators=(',', ':'))


def owner(j, W):
    return int(hashlib.sha1(json.dumps(j['key'], separators=(',', ':')).encode()).hexdigest(), 16) % W


def rec_key(kind, r):
    if kind == 'ctx':
        return json.dumps(['c', [r['ctx'], r['dirs'], r['t']], r['T']], separators=(',', ':'))
    return None


def run(a):
    os.makedirs(OUTD, exist_ok=True)
    gi = os.path.join(OUTD, '.gitignore')
    if not os.path.exists(gi):
        open(gi, 'w').write('# worker files of split231.py (published on xfer/231x/*)\n*\n!.gitignore\n')
    me = f'w{a.index}'
    paths = {k: os.path.join(OUTD, f'{k}_{me}.jsonl') for k in ('ctx', 'plain')}
    try:
        if me in F.ls_remote():
            tr = F.fetch_trees([me], {}).get(me, {})
            for k, p in paths.items():
                raw = tr.get(f'{k}.jsonl.gz')
                if raw:
                    n = F.union_into(p, [l for l in gzip.decompress(raw).decode().split('\n') if l.strip()])
                    F.log(f'merged {n} {k} records from xfer/231x/{me}')
    except (RuntimeError, OSError) as e:
        F.log(f'restore failed: {str(e)[:200]}')
    done = set()
    for l in F.read_lines(paths['ctx']):
        done.add(rec_key('ctx', json.loads(l)))
    for l in F.read_lines(paths['plain']):
        r = json.loads(l); done.add(json.dumps(['p', [r['dirs'], [C.GA.sym_of(tuple(x)) for x in r['alpha']]], None],
                                              separators=(',', ':')))
    jobs = [json.loads(l) for l in gzip.open(a.jobs, 'rt') if l.strip()]
    mine = [j for j in jobs if owner(j, a.workers) == a.index and jkey(j) not in done]
    F.log(f'worker {a.index}/{a.workers}: {len(mine)} jobs to run ({len(jobs)} in the file)')
    t_end = time.time() + a.hours * 3600
    G = dict(paths=paths, t_end=t_end)

    def gen():
        for j in mine:
            if time.time() > t_end or os.path.exists(os.path.join(OUTD, 'STOP')):
                return
            yield dict(j, _paths=paths, _t_end=t_end)

    import multiprocessing as mp
    pool = mp.get_context('fork').Pool(a.procs, maxtasksperchild=50)
    last = time.time()
    for j, r in pool.imap_unordered(work, gen()):
        F.log(f"{j['kind']} {j['key']} T={j.get('T')}: {r['result']} {r['seconds']}s")
        if time.time() - last > a.publish_min * 60:
            publish(me, paths); last = time.time()
    pool.close(); pool.join()
    publish(me, paths)
    F.log('done')


def work(j):
    paths, t_end = j.pop('_paths'), j.pop('_t_end')
    tl = min(j.get('tl', 600), max(30, t_end - time.time()))
    if j['kind'] == 'c':
        ctx, c, t = j['key']
        r = S7.thr(tuple(c), tuple(t), int(j['T']), int(ctx), tl=tl, path=paths['ctx'])
    else:
        SV.OPL = paths['plain']
        r = SV.plain(C.fp.lkey(tuple(j['key'][0]), tuple(j['key'][1])), tl=tl)
    return j, r


def publish(me, paths):
    files = {}
    for k, p in paths.items():
        ls = F.read_lines(p)
        if ls:
            files[f'{k}.jsonl.gz'] = gzip.compress(('\n'.join(ls) + '\n').encode(), 9, mtime=0)
    if not files:
        return
    files['record.json'] = json.dumps(dict(worker=me, time=time.strftime('%Y-%m-%dT%H:%M:%SZ', time.gmtime()))).encode()
    try:
        tip = F.ls_remote().get(me)
        F.push_tree(me, files, tip, f'split231 {me}')
        F.log(f'published to xfer/231x/{me}')
    except (RuntimeError, OSError) as e:
        F.log(f'publish failed: {str(e)[:200]}')


def collect():
    tips = F.ls_remote()
    names = sorted(n for n in tips if n.startswith('w'))
    trees = F.fetch_trees(names, tips)
    out = {'ctx': set(), 'plain': set()}
    for n in names:
        for k in out:
            raw = trees.get(n, {}).get(f'{k}.jsonl.gz')
            if raw:
                out[k] |= {l for l in gzip.decompress(raw).decode().split('\n') if l.strip()}
    return names, out


def status(a):
    names, out = collect()
    import collections
    for k, ls in out.items():
        c = collections.Counter(json.loads(l)['result'] for l in ls)
        print(k, len(ls), dict(c))
    print(len(names), 'branches')


def merge(a):
    names, out = collect()
    for k, fn in (('ctx', 'ctxshare_s231.jsonl.gz'), ('plain', 'oracle_plain_s231.jsonl.gz')):
        p = os.path.join(HERE, 'data', fn)
        old = set()
        if os.path.exists(p):
            old = {l for l in gzip.open(p, 'rt').read().split('\n') if l.strip()}
        ls = sorted(old | out[k])
        with gzip.GzipFile(p, 'wb', mtime=0) as g:
            g.write(('\n'.join(ls) + '\n').encode())
        print('wrote', p, len(ls))


def main():
    ap = argparse.ArgumentParser()
    sp = ap.add_subparsers(dest='cmd', required=True)
    p = sp.add_parser('run')
    p.add_argument('--index', type=int, required=True); p.add_argument('--workers', type=int, required=True)
    p.add_argument('--hours', type=float, required=True); p.add_argument('--procs', type=int, default=4)
    p.add_argument('--publish-min', type=float, default=10); p.add_argument('--jobs', default=JOBS)
    sp.add_parser('status'); sp.add_parser('merge')
    a = ap.parse_args()
    {'run': run, 'status': status, 'merge': merge}[a.cmd](a)


if __name__ == '__main__':
    main()
