"""Plain-decide k6/H9 keys (lazy-cut, radius 4) with a wall-clock limit, one process per key.

  nice -n 10 python decide234.py JOBS.jsonl OUT.jsonl [TL]          (driver)
  python decide234.py --one KIND DIRS SYMS                          (worker)
"""
import sys, os, json, time, subprocess
sys.dont_write_bytecode = True


def one(kind, ds, syms):
    import k7
    enc = k7.encoding((kind, tuple(ds), tuple(syms)))
    t = time.time()
    st, _, cuts = k7.W.decide(enc, certify=False)
    return dict(kind=kind, dirs=ds, syms=syms, result=st, seconds=round(time.time() - t, 3), cuts=cuts)


def main():
    if sys.argv[1] == '--one':
        print(json.dumps(one(sys.argv[2], json.loads(sys.argv[3]), json.loads(sys.argv[4]))))
        return
    jobs, out = sys.argv[1], sys.argv[2]
    tl = float(sys.argv[3]) if len(sys.argv) > 3 else 120
    done = set()
    if os.path.exists(out):
        done = {(r['kind'], tuple(r['dirs']), tuple(r['syms'])) for r in map(json.loads, open(out))}
    here = os.path.dirname(os.path.abspath(__file__))
    for j in map(json.loads, open(jobs)):
        k = (j['kind'], tuple(j['dirs']), tuple(j['syms']))
        if k in done:
            continue
        try:
            p = subprocess.run([sys.executable, os.path.join(here, 'decide234.py'), '--one', j['kind'],
                                json.dumps(j['dirs']), json.dumps(j['syms'])], capture_output=True, text=True, timeout=tl)
            r = json.loads(p.stdout)
        except subprocess.TimeoutExpired:
            r = dict(kind=j['kind'], dirs=j['dirs'], syms=j['syms'], result='TIMEOUT', seconds=tl)
        done.add(k)
        with open(out, 'a') as f:
            f.write(json.dumps(r, separators=(',', ':')) + '\n')
        print(json.dumps(r), flush=True)


if __name__ == '__main__':
    main()
