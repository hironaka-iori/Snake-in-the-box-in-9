import sys, json, itertools
from concurrent.futures import ProcessPoolExecutor
sys.path.insert(0, '/home/user/Snake-in-the-box-in-9/milestones/07-window-223/scripts')
import local_window_search as lws
BAD = {(1,1),(1,2),(2,1),(1,3),(3,1)}
def ok(p):
    return all((p[i], p[i+1]) not in BAD for i in range(2)) and p != (2,2,2)
def job(args):
    radius, shape, p, secs = args
    r = lws.run(radius, shape, p, secs)
    return dict(radius=radius, shape=shape, alpha=p, status=r['status'], t=round(r['elapsed_seconds'],2), cuts=len(r['cycle_cuts']))
if __name__ == '__main__':
    radius = int(sys.argv[1]); maxsum = int(sys.argv[2]); secs = float(sys.argv[3])
    pats = [p for p in itertools.product(range(1,7), repeat=3) if sum(p) <= maxsum and p[0] <= p[2] and ok(p)]
    pats.append((2,2,2))
    jobs = [(radius, s, p, secs) for p in pats for s in ('repeated','distinct')]
    out = []
    with ProcessPoolExecutor(4) as ex:
        for r in ex.map(job, jobs):
            print(r, flush=True); out.append(r)
    json.dump(out, open(f'/tmp/claude-0/-home-user-Snake-in-the-box-in-9/54df6b79-3551-5be0-97ec-edf141639c5c/scratchpad/ana/patterns_r{radius}_s{maxsum}.json','w'), indent=1)
