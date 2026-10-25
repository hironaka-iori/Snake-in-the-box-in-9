"""Measure the replay hints of many keys in parallel (cost234.replay_cost), resumable.

  nice -n 10 python measure234.py JOBS.jsonl OUT.jsonl [WORKERS] [--decide-only]
JOBS: one {"kind","dirs","syms"} per line.  OUT gets one record per key (already measured keys
are skipped).  --decide-only: lazy-cut plain solve and solve time only (no proof).
"""
import sys, os, json, time, tempfile, multiprocessing as mp
sys.dont_write_bytecode = True
import cost234 as C
import k7


def work(job):
    k = (job['kind'], tuple(job['dirs']), tuple(job['syms']))
    while C.disk_mb() < 450:
        time.sleep(30)
    wd = tempfile.mkdtemp(dir=C.SCR)
    try:
        if DECIDE:
            enc = k7.encoding(k); t = time.time()
            st, _, cuts = k7.W.decide(enc, certify=False)
            return dict(kind=k[0], dirs=list(k[1]), syms=list(k[2]), result=st, solve_s=round(time.time() - t, 3), cuts=cuts)
        return C.replay_cost(k, wd=wd)
    except Exception as e:
        return dict(kind=k[0], dirs=list(k[1]), syms=list(k[2]), error=str(e)[:300])
    finally:
        for f in os.listdir(wd):
            os.remove(os.path.join(wd, f))
        os.rmdir(wd)


DECIDE = '--decide-only' in sys.argv


def main():
    jobs, out = sys.argv[1], sys.argv[2]
    nw = int(sys.argv[3]) if len(sys.argv) > 3 and sys.argv[3].isdigit() else 3
    done = set()
    if os.path.exists(out):
        for l in open(out):
            r = json.loads(l)
            done.add((r['kind'], tuple(r['dirs']), tuple(r['syms'])))
    todo = [j for j in map(json.loads, open(jobs)) if (j['kind'], tuple(j['dirs']), tuple(j['syms'])) not in done]
    print(f'{len(todo)} to do, {len(done)} done', flush=True)
    t0 = time.time(); n = 0
    with mp.Pool(nw, maxtasksperchild=200) as p, open(out, 'a') as f:
        for r in p.imap_unordered(work, todo, chunksize=1):
            f.write(json.dumps(r, separators=(',', ':')) + '\n'); f.flush()
            n += 1
            if n % 200 == 0:
                print(f'{n} / {len(todo)}, {time.time() - t0:.0f}s', flush=True)
    print('done', n, round(time.time() - t0), flush=True)


if __name__ == '__main__':
    main()
