import sys, json
from concurrent.futures import ProcessPoolExecutor
sys.path.insert(0, '/home/user/Snake-in-the-box-in-9/milestones/07-window-223/scripts')
import local_window_search as lws
def job(p):
    r = lws.run(4, 'distinct', p, 900)
    return dict(alpha=p, status=r['status'], t=round(r['elapsed_seconds'], 1), cuts=len(r['cycle_cuts']), ball=r['ball_size'])
if __name__ == '__main__':
    pats = [(2,3,3), (2,4,2), (3,2,4)]
    with ProcessPoolExecutor(3) as ex:
        res = list(ex.map(job, pats))
    for r in res: print(r)
    json.dump(res, open('patterns_r4.json', 'w'))
