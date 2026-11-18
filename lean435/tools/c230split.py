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

Work stealing (18 Nov): any number of machines run

    c230split.py --steal --index K [--cpus 4] [--mem-gb 12] [--hours 48]

The work is cut into UNITS: prep:N (prepare + pack, one machine), part:N:k (one part module), final:N.
A unit is available when its inputs are on the remote: prep when src-N is missing, part k when src-N is
there and N-k<k> is not, final when every part is there and N is not published. Units are claimed on
xfer/c230splitclaim/h<K> (prod435 Claims: TTL --claim-ttl h, renewed every 5 min, the earlier claim wins),
so no unit is done twice and a dead machine's units come back. Order: finals, then parts (items whose
sources this machine already has first, then largest item first), then preps (largest first) when fewer
than 2 x --cpus x (stealers seen in the claims) unclaimed parts are left in the farm; then preps go
before parts. Cost per unit: prep 2 cores and 3 GB (bigreplay --jobs 3), part 1 core and
its predicted peak (1.3 x the largest RssAnon of the item's published parts, 2.5-6.5 GB; 6.0 GB while
fewer than 2 are published; measured max 5.81 GB over 304 parts), final 1 core and 4 GB, one final at a time.
Units start while the cores (--cpus) and the predicted memory (--mem-gb) allow; beyond --mem-gb, up to
--over-n parts may start while MemAvailable covers them + --over-free-gb (2), and the youngest of them is
killed and requeued when MemAvailable falls below --over-kill-gb (1). Finals publish to
xfer/c230help/w<600+K>. Several part processes of one item share its base modules (Cnf, D*, Ps), built
once under a lock (splitfarm435.base_lock). The static mode above does not claim: stop the static
machines and relaunch them with --steal (their published sources and parts are kept and reused). Until
then a stealer skips the parts of an item with a part pushed in the last --static-window min (60) and no
stealer claim on it (a static machine is on it); preps are not protected that way. A stealer restarted
by PID (its unit processes left running) adopts them: keeps them claimed while they live, and does not
start them again.
"""
import argparse, os, shutil, subprocess, sys, time

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.abspath(os.path.join(HERE, '..', '..'))
LIST = os.path.join(ROOT, 'milestones', '37-230-feasibility', 'data', 'c230_split_items.txt')
sys.path.insert(0, HERE)
sys.dont_write_bytecode = True


def log(msg):
    print(time.strftime('%H:%M:%S ') + msg, flush=True)


def steal(a):
    import json, re
    import splitfarm435 as SF
    P = SF.P
    items = sorted(((n, float(e)) for n, e, _r in (l.split() for l in open(LIST) if l.strip())), key=lambda x: -x[1])
    est = dict(items)
    order = {n: i for i, (n, _e) in enumerate(items)}
    claims = P.Claims(P.PFX.rstrip('/') + 'splitclaim/', 'h', a.index, a.claim_ttl)
    repo = P.Repo(SF.SPFX)
    scan = P.Scan([P.PFX, P.HELP_PFX])
    gb_dir = os.path.join(P.HOME, 'splitsteal.git')      # partial fetches of trees and small blobs (own repo:
    if not os.path.exists(os.path.join(gb_dir, 'HEAD')):  # scan.git is also fetched into by unit processes)
        os.makedirs(gb_dir, exist_ok=True)
        P.git('init', '-q', '--bare', gb_dir)
    sf = [sys.executable, os.path.join(HERE, 'splitfarm435.py')]
    plan = os.environ['C230_PLAN']
    nparts, peak_cache, push_time = {}, {}, {}
    running = {}                                         # unit -> (Popen, cpus, gb, t0, logfile)
    failed = {}
    preempted, cooldown = set(), {}
    published, tips = set(), {}
    local_items = {n for n, _e in items if os.path.isdir(SF.wd(n))}
    last = dict(tips=0, pub=0, claims=0, beat=0)
    t_end = time.time() + a.hours * 3600
    stopf = os.path.join(P.HOME, 'STOP_SPLIT')
    logdir = os.path.join(P.HOME, 'split-logs')
    os.makedirs(logdir, exist_ok=True)
    log(f'split stealer h{a.index}: {len(items)} split items, --cpus {a.cpus}, --mem-gb {a.mem_gb}')

    def unit_pids():
        # live splitfarm435 unit processes on this machine (e.g. left running by a stealer restarted by PID)
        out = {}
        for d in os.listdir('/proc'):
            if not d.isdigit():
                continue
            try:
                c = open(f'/proc/{d}/cmdline', 'rb').read().split(b'\0')
            except OSError:
                continue
            c = [x.decode('utf-8', 'replace') for x in c if x]
            if not any(x.endswith('splitfarm435.py') for x in c):
                continue
            i = next(j for j, x in enumerate(c) if x.endswith('splitfarm435.py'))
            kind, n = c[i + 1] if len(c) > i + 1 else '', c[c.index('--name') + 1] if '--name' in c else ''
            if kind == 'prepare':
                out['prep:' + n] = int(d)
            elif kind == 'final':
                out['final:' + n] = int(d)
            elif kind == 'part' and '--k' in c:
                out[f'part:{n}:{c[c.index("--k") + 1]}'] = int(d)
        return out
    adopted = unit_pids()                                # unit -> pid: kept claimed (renewed) while alive
    if adopted:
        for u in adopted:
            claims.mine[u] = time.time()
        claims.write()
        log(f'adopted {len(adopted)} running unit(s) of an earlier run: {sorted(adopted)}')

    def tree(t):
        P.git('fetch', '-q', '--depth', '1', '--filter=blob:none', repo.url, t, cwd=gb_dir, timeout=300)
        return {l.split('\t')[1]: l.split()[2] for l in P.git('ls-tree', t, cwd=gb_dir).splitlines()}

    def blob(x):
        if subprocess.run(['git', 'cat-file', '-e', x], cwd=gb_dir, capture_output=True).returncode != 0:
            P.git('fetch', '-q', '--filter=blob:none', repo.url, x, cwd=gb_dir, timeout=300)
        return P.git('cat-file', 'blob', x, cwd=gb_dir)

    def parts_of(n):
        if n not in nparts:
            ent = tree(tips[f'src-{n}'])
            nparts[n] = len([p for p in ent if re.search(r'\.K\d+\.lean\.gz$', p)])
        return nparts[n]

    def part_gb(n):
        # 1.3 x the largest peak of ALL its published parts (later parts are often larger: V012034A45436
        # k10 3.9 GB against 3.7 for k0-k9), at least 2.5 GB, at most 6.5; 6.0 GB with fewer than 2 published
        refs = sorted(r for r in tips if r.startswith(n + '-k'))
        key = tuple(tips[r] for r in refs)
        if peak_cache.get(n, (None,))[0] != key:
            peaks = dict(peak_cache.get(n, (None, None, {}))[2])
            for r in refs:
                if tips[r] in peaks:
                    continue
                try:
                    ent = tree(tips[r])
                    peaks[tips[r]] = max(json.loads(l)['anon_gb'] for l in blob(ent['build-log.jsonl']).splitlines() if l.strip())
                except Exception:  # noqa: BLE001
                    pass
            g = min(6.5, max(2.5, 1.3 * max(peaks.values()))) if len(peaks) >= 2 else 6.0
            peak_cache[n] = (key, g, peaks)
        return peak_cache[n][1]

    def static_active(n):
        # a static machine (no claims) is building parts of n: a part of n was pushed in the last
        # --static-window min and no unit of n is claimed by a stealer; time-bounded, so nothing starves
        if not a.avoid_static or any(u.split(':')[1] == n for u in list(claims.busy()) + list(claims.mine)):
            return False
        refs = [tips[r] for r in tips if r.startswith(n + '-k')]
        if not refs:
            return False
        key = tuple(sorted(refs))
        if push_time.get(n, (None,))[0] != key:
            try:
                P.git('fetch', '-q', '--depth', '1', '--filter=blob:none', repo.url, *refs, cwd=gb_dir, timeout=300)
                push_time[n] = (key, max(int(P.git('log', '-1', '--format=%ct', x, cwd=gb_dir).strip()) for x in refs))
            except Exception:  # noqa: BLE001
                return True
        return time.time() - push_time[n][1] < a.static_window * 60

    def units():
        out = []
        for n, _e in items:
            if 'LocalWindowCert.' + n in published:
                continue
            if f'src-{n}' not in tips:
                out.append(('prep:' + n, 'prep', n, None))
                continue
            try:
                K = parts_of(n)
            except Exception as e:  # noqa: BLE001
                log(f'{n}: cannot list its sources ({str(e)[:120]})')
                continue
            miss = [k for k in range(K) if f'{n}-k{k}' not in tips]
            if miss and static_active(n):
                continue
            if miss:
                out += [(f'part:{n}:{k}', 'part', n, k) for k in miss]
            else:
                out.append(('final:' + n, 'final', n, None))
        return out

    while True:
        now = time.time()
        try:
            if now - last['tips'] > 60:
                tips = repo.ls()
                last['tips'] = now
            if now - last['pub'] > 300:
                published = scan.refresh()[0]
                last['pub'] = now
            if now - last['claims'] > 60:
                claims.read()
                last['claims'] = now
                # the tie rule again at every read (a delayed push): a unit of mine that another machine
                # claimed first is stopped and dropped (as prod435 run does)
                for u in [u for u in running if u not in preempted and not claims.wins(u)]:
                    preempted.add(u)
                    for c_ in P.descendants(running[u][0].pid) + [running[u][0].pid]:
                        try:
                            os.kill(c_, 9)
                        except OSError:
                            pass
                    log(f'{u}: claimed earlier by another machine: stopped')
            if now - last['beat'] > 300 and claims.mine:
                claims.write()
                last['beat'] = now
        except Exception as e:  # noqa: BLE001
            log(f'refresh failed (kept the last state): {str(e)[:200]}')
        # collect
        for u in list(running):
            pr, c, g, t0, lf, ov = running[u]
            if pr.poll() is None:
                continue
            del running[u]
            if u in preempted:
                preempted.discard(u)
                log(f'{u}: stopped (preempted or lost its claim)')
                claims.drop([u])
                cooldown[u] = time.time() + 900          # not retried here for 15 min (no thrash)
            elif pr.returncode == 0:
                log(f'{u}: done in {time.time() - t0:.0f} s')
                claims.published([u])
                if u.startswith('prep:'):               # sources pushed: the LRAT and generation files go
                    shutil.rmtree(os.path.join(SF.wd(u[5:]), 'prep'), ignore_errors=True)
            else:
                failed[u] = failed.get(u, 0) + 1
                log(f'{u}: FAILED (exit {pr.returncode}, try {failed[u]}); log {lf}')
                claims.drop([u])
            last['tips'] = 0
        for u, pid in list(adopted.items()):
            if not os.path.exists(f'/proc/{pid}'):
                del adopted[u]
                log(f'{u}: adopted unit ended')
                claims.published([u])                  # failed or not: its outputs decide (tips) after the keep time
                last['tips'] = 0
        # over units (started beyond --mem-gb on measured free memory): below --over-kill-gb MemAvailable the
        # youngest is killed and goes back to the queue (not counted as a failure)
        # (if no over unit runs: the youngest part, adopted or not, rather than the kernel's OOM killer, which
        # takes the largest process, i.e. usually the oldest part)
        if P.mem_available_gb() < a.over_kill_gb:
            ov = [u for u, v in running.items() if v[5] and u not in preempted]
            parts_ = [u for u in running if u.startswith('part:') and u not in preempted]
            if ov or parts_:
                u = max(ov or parts_, key=lambda x: running[x][3])
                preempted.add(u)
                for c_ in P.descendants(running[u][0].pid) + [running[u][0].pid]:
                    try:
                        os.kill(c_, 9)
                    except OSError:
                        pass
                log(f'{u}: {P.mem_available_gb():.1f} GiB free: preempting this unit')
            else:
                ad = [u for u in adopted if u.startswith('part:')]
                if ad:
                    u = max(ad, key=lambda x: adopted[x])           # youngest (highest pid)
                    for c_ in P.descendants(adopted[u]) + [adopted[u]]:
                        try:
                            os.kill(c_, 9)
                        except OSError:
                            pass
                    del adopted[u]
                    claims.drop([u])
                    cooldown[u] = time.time() + 900
                    log(f'{u}: {P.mem_available_gb():.1f} GiB free: preempting this adopted unit')
        stop = os.path.exists(stopf) or now > t_end
        avail = [x for x in units() if x[0] not in running and x[0] not in adopted and failed.get(x[0], 0) < 2]
        if not avail and not running and not adopted:
            log('no split unit left: ending')
            break
        if stop and not running and not adopted:
            log('stop: ending')
            break
        for n in list(local_items):                        # published items: their local files go
            if 'LocalWindowCert.' + n in published and not any(u.split(':')[1] == n for u in running):
                shutil.rmtree(SF.wd(n), ignore_errors=True)
                local_items.discard(n)
        busy = claims.busy()
        st = os.statvfs(P.HOME)
        disk_gb = st.f_bavail * st.f_frsize / 2**30
        free = [x for x in avail if x[0] not in busy and x[0] not in claims.mine and cooldown.get(x[0], 0) < now]
        cost = lambda u: (2, 3.0) if u.startswith('prep:') else (1, 4.0 if u.startswith('final:') else 6.0)  # noqa: E731
        cpus = a.cpus - sum(v[1] for v in running.values()) - sum(cost(u)[0] for u in adopted)
        mem = a.mem_gb - sum(v[2] for v in running.values() if not v[5]) - sum(cost(u)[1] for u in adopted)
        nfinal = sum(1 for u in list(running) + list(adopted) if u.startswith('final:'))
        nparts_free = sum(1 for x in free if x[1] == 'part')
        # preps gate everything (most items have no sources yet): they go before parts while the farm's
        # backlog of unclaimed parts is below 2 parts per core of the stealers seen in the claims
        nstealers = 1 + sum(1 for nm, (_t, c) in claims.cache.items()
                            if any(now - v[1] < claims.ttl for v in c.values()))
        prep_first = nparts_free < 2 * a.cpus * nstealers
        local = lambda n: os.path.exists(os.path.join(SF.wd(n), 'src'))  # noqa: E731
        rank = {'final': 0, 'prep': 1, 'part': 2} if prep_first else {'final': 0, 'part': 1, 'prep': 2}
        pick = sorted(free, key=lambda x: (rank[x[1]], not local(x[2]), order[x[2]], x[3] or 0))
        batch = []
        for u, kind, n, k in pick:
            if stop:
                break
            c, g = {'prep': (2, 3.0), 'final': (1, 4.0)}.get(kind) or (1, part_gb(n))
            if kind == 'final' and (nfinal or any(b[1] == 'final' for b in batch)):
                continue
            if kind == 'prep' and (not prep_first or disk_gb < a.prep_disk_gb):
                continue
            if disk_gb < a.min_disk_gb:
                continue
            over = False
            if c > cpus:
                continue
            if g > mem and (running or batch):
                # over admission (parts only): measured free memory covers it, the other over units' predictions
                # and --over-free-gb; preemptible (see above)
                nover = sum(1 for v in running.values() if v[5]) + sum(1 for b in batch if b[6])
                over_gb = sum(v[2] for v in running.values() if v[5]) + sum(b[5] for b in batch if b[6])
                if kind != 'part' or nover >= a.over_n or P.mem_available_gb() < g + over_gb + a.over_free_gb:
                    continue
                over = True
            batch.append((u, kind, n, k, c, g, over))
            cpus -= c
            if not over:
                mem -= g
        if batch:
            keep = set(claims.claim([b[0] for b in batch]))
            for u, kind, n, k, c, g, over in batch:
                if u not in keep:
                    log(f'{u}: claimed by another machine')
                    continue
                if kind == 'prep':
                    cmd = sf + ['prepare', '--plan', plan, '--name', n, '--jobs', '3',
                                '--parts', str(a.big_parts if est[n] > a.big else a.parts)]
                elif kind == 'part':
                    cmd = sf + ['part', '--name', n, '--jobs', '2', '--rss-gb', str(a.rss_gb), '--k', str(k)]
                else:
                    cmd = sf + ['final', '--name', n, '--plan', plan, '--index', str(a.publish_index + a.index),
                                '--require-remote']
                lf = os.path.join(logdir, u.replace(':', '_') + '.log')
                local_items.add(n)
                running[u] = (subprocess.Popen(cmd, stdout=open(lf, 'a'), stderr=subprocess.STDOUT), c, g, time.time(), lf,
                              over)
                log(f'{u}: started ({c} core(s), {g:.1f} GB predicted{", over the budget, preemptible" if over else ""})')
        time.sleep(5)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--index', type=int, required=True)
    ap.add_argument('--of', type=int, default=None, help='static mode: machine --index of --of')
    ap.add_argument('--steal', action='store_true', help='work stealing over units (see the docstring)')
    ap.add_argument('--cpus', type=int, default=4)
    ap.add_argument('--mem-gb', type=float, default=12)
    ap.add_argument('--hours', type=float, default=48)
    ap.add_argument('--claim-ttl', type=float, default=2.0)
    ap.add_argument('--prep-disk-gb', type=float, default=12, help='start a prep only with this much free disk')
    ap.add_argument('--min-disk-gb', type=float, default=4)
    ap.add_argument('--no-avoid-static', dest='avoid_static', action='store_false',
                    help='do not skip items a static (non-claiming) machine is working on')
    ap.add_argument('--static-window', type=float, default=60, help='minutes (see static_active)')
    ap.add_argument('--over-free-gb', type=float, default=2.0, help='MemAvailable kept beyond an over part')
    ap.add_argument('--over-kill-gb', type=float, default=1.0, help='preempt the youngest over part below this')
    ap.add_argument('--over-n', type=int, default=2, help='at most this many over parts at once')
    ap.add_argument('--parts', type=int, default=8)
    ap.add_argument('--big-parts', type=int, default=16)
    ap.add_argument('--big', type=float, default=35e6)
    ap.add_argument('--jobs', type=int, default=2, help='parts built at once (one lean each)')
    ap.add_argument('--rss-gb', type=float, default=6.5, help='RssAnon cap per part (pilot peak 3.7 GB at 30.8 M hints)')
    ap.add_argument('--publish-index', type=int, default=None, help='finals publish to <help>/w<this + index> '
                    '(default 500 static, 600 --steal)')
    a = ap.parse_args()
    for v in ('PROD435_ADAPTER', 'PROD435_CERT', 'PROD435_PFX', 'C230_PLAN'):
        if not os.environ.get(v):
            raise SystemExit(f'set ${v} (see milestones/37-230-feasibility/PILOT.md)')
    if 'c230' not in os.environ['PROD435_PFX']:
        raise SystemExit('PROD435_PFX is not the c230 family')
    if a.publish_index is None:
        a.publish_index = 600 if a.steal else 500
    if a.steal:
        return steal(a)
    if a.of is None:
        raise SystemExit('--of is required without --steal')
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
