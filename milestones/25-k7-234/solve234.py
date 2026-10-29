"""Decide or replay-measure many keys in parallel with a per-key wall-clock limit, resumable.

  nice -n 10 python solve234.py decide|replay JOBS.jsonl OUT.jsonl [--workers 3] [--tl 120]

JOBS: one {"kind","dirs","syms"} per line (kind 'k6', 'H' or 'F').  Keys already in OUT are
skipped.  decide: lazy-cut plain solve (radius 4), record {kind,dirs,syms,result,seconds,cuts}
(the format of data/decide234.jsonl).  replay: cost234.replay_cost (proofs streamed through a
FIFO, never stored).  Each worker runs in its own process group; a key over the limit is
recorded as TIMEOUT and its worker group is killed by its PID and replaced.  Workers pause
while the disk has less than 450 MB free.
"""
import sys, os, json, time, signal, shutil, tempfile, argparse, queue
import multiprocessing as mp
sys.dont_write_bytecode = True


def kkey(j):
    return (j['kind'], tuple(j['dirs']), tuple(j['syms']))


def worker(wid, mode, inq, outq):
    os.setsid()
    import k7
    import cost234 as C
    while True:
        j = inq.get()
        if j is None:
            return
        while C.disk_mb() < 450:
            time.sleep(30)
        wd = tempfile.mkdtemp(dir=C.SCR)
        outq.put(('start', wid, j, wd, time.time()))
        k = kkey(j)
        try:
            if mode == 'decide':
                enc = k7.encoding(k); t = time.time()
                st, _, cuts = k7.W.decide(enc, certify=False)
                r = dict(kind=k[0], dirs=list(k[1]), syms=list(k[2]), result=st, seconds=round(time.time() - t, 3),
                         cuts=cuts)
            else:
                r = C.replay_cost(k, wd=wd)
        except Exception as e:
            r = dict(kind=k[0], dirs=list(k[1]), syms=list(k[2]), error=str(e)[:300])
        shutil.rmtree(wd, ignore_errors=True)
        outq.put(('done', wid, r, None, None))


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('mode', choices=['decide', 'replay']); ap.add_argument('jobs'); ap.add_argument('out')
    ap.add_argument('--workers', type=int, default=3); ap.add_argument('--tl', type=float, default=120)
    a = ap.parse_args()
    done = set()
    if os.path.exists(a.out):
        done = {kkey(json.loads(l)) for l in open(a.out)}
    todo, seen = [], set()
    for j in map(json.loads, open(a.jobs)):
        k = kkey(j)
        if k not in done and k not in seen:
            seen.add(k); todo.append(dict(kind=k[0], dirs=list(k[1]), syms=list(k[2])))
    print(f'{len(todo)} to do, {len(done)} done', flush=True)
    inq, outq = mp.Queue(), mp.Queue()
    for j in todo:
        inq.put(j)
    for _ in range(a.workers):
        inq.put(None)
    procs, cur = {}, {}

    def spawn(wid):
        p = mp.Process(target=worker, args=(wid, a.mode, inq, outq), daemon=False)
        p.start(); procs[wid] = p

    for w in range(a.workers):
        spawn(w)
    n, t0 = 0, time.time()
    with open(a.out, 'a') as f:
        def emit(r):
            nonlocal n
            f.write(json.dumps(r, separators=(',', ':')) + '\n'); f.flush()
            n += 1
            if n % 200 == 0:
                print(f'{n} / {len(todo)}, {time.time() - t0:.0f}s', flush=True)
        while procs:
            try:
                tag, wid, x, wd, ts = outq.get(timeout=1)
                if tag == 'start':
                    cur[wid] = (x, wd, ts)
                else:
                    cur.pop(wid, None); emit(x)
            except queue.Empty:
                pass
            now = time.time()
            for wid, (j, wd, ts) in list(cur.items()):
                if now - ts > a.tl:
                    try:
                        os.killpg(procs[wid].pid, signal.SIGKILL)
                    except ProcessLookupError:
                        pass
                    procs[wid].join()
                    shutil.rmtree(wd, ignore_errors=True)
                    cur.pop(wid)
                    emit(dict(j, result='TIMEOUT', seconds=a.tl))
                    spawn(wid)
            for wid, p in list(procs.items()):
                if not p.is_alive() and wid not in cur:
                    p.join(); procs.pop(wid)
    print('done', n, round(time.time() - t0), flush=True)


if __name__ == '__main__':
    main()
