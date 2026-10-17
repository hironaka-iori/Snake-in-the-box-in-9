import sys, json
sys.dont_write_bytecode = True
sys.path.insert(0, '/home/user/Snake-in-the-box-in-9/milestones/07-window-223/scripts')
import local_window_search as lws
from concurrent.futures import ProcessPoolExecutor

def job(a):
    radius, shape, p, secs = a
    r = lws.run(radius, shape, p, secs)
    out = dict(radius=radius, shape=shape, alpha=p, status=r['status'], t=round(r['elapsed_seconds'], 2),
               cuts=len(r['cycle_cuts']), ball=r['ball_size'])
    if 'selected_vertices' in r:
        out['selected'] = r['selected_vertices']
        out['n_components'] = len(r['components'])
    return out

if __name__ == '__main__':
    spec = json.loads(sys.argv[1])
    outpath = sys.argv[2]
    workers = int(sys.argv[3]) if len(sys.argv) > 3 else 4
    jobs = [tuple(j) for j in spec]
    res = []
    with ProcessPoolExecutor(workers) as ex:
        for r in ex.map(job, jobs):
            print({k: v for k, v in r.items() if k != 'selected'}, flush=True)
            res.append(r)
    json.dump(res, open(outpath, 'w'))
