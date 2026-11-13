#!/usr/bin/env python3
"""Keep the cores busy during the 233 certificate production by adding and retiring
`pregen233.py` workers.

Every --interval seconds it counts the busy processes, `lean` (builds of prod's guarded build) plus
running `cert233.py replay` generations (prod's own and the workers'); each uses about one core.

* busy < --cores, MemAvailable >= --start-mem-gb, free disk >= --min-disk-mb + 500, and no start in
  the last --start-gap seconds: start a worker with the lowest free index (at most --max-workers).
* busy > --cores + --over and more than --min-workers workers: ask the newest worker to stop after
  its current item (touch $CERT233_SCR/pregen_stop<i>; one request at a time).
* Workers already running when it starts (older code without the stop file) are stopped as soon
  as they are between two items (no replay child); the rules above then start new ones.
* MemAvailable < --kill-mem-gb: kill the newest worker above --min-workers now, with its replay,
  and release its claim (its item is redone later).

Workers it starts use `--min-disk-mb` (they exit below it).  It never touches prod or the builds; it also
works while prod is stopped (workers exit by themselves once everything is built).
Log: JSON lines on stdout.

  CERT233_SCR=/home/user/cert233work setsid nohup python3 supervisor233.py >> $CERT233_SCR/logs/supervisor.log 2>&1 &
"""
import argparse, json, os, re, shutil, signal, subprocess, sys, time

HERE = os.path.dirname(os.path.abspath(__file__))
BASE = os.environ.get('CERT233_SCR', '/home/user/cert233work')
LEANBIN = '/home/user/lean-deps/toolchain/lean-4.19.0-linux/bin'


def log(**r):
    print(json.dumps({'t': round(time.time()), **r}), flush=True)


def mem_avail_gb():
    for line in open('/proc/meminfo'):
        if line.startswith('MemAvailable:'):
            return int(line.split()[1]) / 2 ** 20
    return 0.0


def procs():
    out = subprocess.run(['ps', '-eo', 'pid=,ppid=,comm=,args='], capture_output=True, text=True).stdout
    rows = []
    for line in out.splitlines():
        p = line.split(None, 3)
        if len(p) == 4:
            rows.append((int(p[0]), int(p[1]), p[2], p[3]))
    return rows


def state():
    rows = procs()
    lean = sum(1 for _, _, c, _ in rows if c == 'lean')
    replays = [(pid, a) for pid, _, _, a in rows if 'cert233.py replay' in a]
    workers = {}
    for pid, _, _, a in rows:
        m = re.search(r'pregen233\.py --worker (\d+)', a)
        if m and 'python' in a.split()[0]:
            workers[int(m.group(1))] = pid
    return lean, replays, workers, rows


def kill_tree(pid, rows):
    for c, pp, _, _ in rows:
        if pp == pid:
            kill_tree(c, rows)
    try:
        os.kill(pid, signal.SIGTERM)
    except ProcessLookupError:
        pass


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--cores', type=int, default=4)
    ap.add_argument('--over', type=int, default=1, help='tolerated oversubscription before retiring')
    ap.add_argument('--min-workers', type=int, default=2)
    ap.add_argument('--max-workers', type=int, default=6)
    ap.add_argument('--start-mem-gb', type=float, default=4.0)
    ap.add_argument('--kill-mem-gb', type=float, default=1.2)
    ap.add_argument('--min-disk-mb', type=int, default=2300)
    ap.add_argument('--start-gap', type=int, default=180)
    ap.add_argument('--interval', type=int, default=60)
    a = ap.parse_args()
    last_start = 0.0
    last_note = None
    legacy = set(state()[2].values())
    next_main = 0.0
    while True:
        try:
            while os.waitpid(-1, os.WNOHANG)[0]:
                pass
        except ChildProcessError:
            pass
        lean, replays, workers, rows = state()
        legacy &= set(workers.values())
        for pid in list(legacy):
            if not any(pp == pid for _, pp, _, _ in rows):
                i = [k for k, v in workers.items() if v == pid][0]
                os.kill(pid, signal.SIGTERM)
                legacy.discard(pid)
                log(action='stop-legacy', worker=i, pid=pid)
        if time.time() < next_main:
            time.sleep(5 if legacy else 1)
            continue
        next_main = time.time() + a.interval
        busy = lean + len(replays)
        mem = mem_avail_gb()
        disk = shutil.disk_usage('/').free // 2 ** 20
        pending = [i for i in workers if os.path.exists(os.path.join(BASE, 'pregen_stop%d' % i))]
        note = dict(lean=lean, replays=len(replays), workers=sorted(workers), mem_gb=round(mem, 1), disk_mb=disk)
        if mem < a.kill_mem_gb and len(workers) > a.min_workers:
            i = max(workers)
            mine = [(pid, ar) for pid, ar in replays if 'pregen%d/out' % i in ar]
            kill_tree(workers[i], rows)
            for pid, ar in mine:
                kill_tree(pid, rows)
                n = ar.split()[-1]
                for f in (os.path.join(BASE, 'pregen_claims', n),
                          os.path.join(BASE, 'pregen%d' % i, 'out', 'LocalWindowUnsat', n + '.lean')):
                    if os.path.exists(f):
                        os.remove(f)
            log(action='kill', worker=i, reason='memory', **note)
        elif (busy > a.cores + a.over and len(workers) - len(pending) > a.min_workers and not pending
              and [k for k, v in workers.items() if v not in legacy]):
            i = max(k for k, v in workers.items() if v not in legacy)
            open(os.path.join(BASE, 'pregen_stop%d' % i), 'w').close()
            log(action='retire', worker=i, **note)
        elif (busy < a.cores and len(workers) < a.max_workers and mem >= a.start_mem_gb
              and disk >= a.min_disk_mb + 500 and time.time() - last_start >= a.start_gap):
            i = min(set(range(a.max_workers)) - set(workers))
            stop = os.path.join(BASE, 'pregen_stop%d' % i)
            if os.path.exists(stop):
                os.remove(stop)
            env = dict(os.environ, CERT233_SCR=BASE, PATH=LEANBIN + ':' + os.environ.get('PATH', ''))
            with open(os.path.join(BASE, 'logs', 'pregen%d.log' % i), 'a') as lf:
                subprocess.Popen(['nice', '-n', '12', sys.executable, os.path.join(HERE, 'pregen233.py'),
                                  '--worker', str(i), '--min-disk-mb', str(a.min_disk_mb)],
                                 cwd=HERE, env=env, stdout=lf, stderr=subprocess.STDOUT, start_new_session=True)
            last_start = time.time()
            log(action='start', worker=i, **note)
        elif note != last_note:
            log(**note)
        last_note = note


if __name__ == '__main__':
    main()
