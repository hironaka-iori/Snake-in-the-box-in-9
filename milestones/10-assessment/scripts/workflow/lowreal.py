import sys, json
sys.dont_write_bytecode = True
from concurrent.futures import ProcessPoolExecutor
import winmin
from shapes import shapes
if __name__ == '__main__':
    S = int(sys.argv[1]); secs = float(sys.argv[2]); out = sys.argv[3]; W = int(sys.argv[4]); m = int(sys.argv[5]) if len(sys.argv) > 5 else 6
    shp = shapes(m)
    res = []
    with ProcessPoolExecutor(W) as ex:
        futs = [ex.submit(winmin.solve, list(s), 9, secs, None, False, 1, 7, S) for s in shp]
        for f in futs:
            r = f.result()
            print(r['shape'], r['status'], r['t'], r['cuts'], (r['best'] or {}).get('alphas'), flush=True)
            res.append(r)
            json.dump(res, open(out, 'w'))
