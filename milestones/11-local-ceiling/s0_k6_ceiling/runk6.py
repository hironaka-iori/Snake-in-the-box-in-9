"""Plain and threshold tests of the extended ceiling windows.  One line per call in results.jsonl.
usage: runk6.py plain|thr  dirs(comma)  radius  [T]  [tl]"""
import sys, os, json, time
sys.dont_write_bytecode = True
from k6lib import wincert, ws
OUT = os.path.join(os.path.dirname(os.path.abspath(__file__)), 'results.jsonl')

def mem_gb():
    for l in open('/proc/meminfo'):
        if l.startswith('MemAvailable'):
            return int(l.split()[1]) / 1e6

def run(kind, ds, radius, T=None, tl=300.0, M=12):
    while mem_gb() < 3.0:
        print('low memory, pausing', flush=True); time.sleep(60)
    k = len(ds) - 1; w = wincert.window_from_dirs(list(ds)); al = [4] * k
    t0 = time.time()
    enc = wincert.Encoding(w, al, radius) if kind == 'plain' else ws.ShareEncoding(w, al, radius, M, T - 1)
    b = time.time() - t0
    st, sel, cuts, sec = ws.solve(enc, tl)
    r = dict(kind=kind, dirs=list(ds), k=k, radius=radius, T=T, M=M, result=st, cuts=cuts, seconds=round(sec, 1),
             build=round(b, 1), nv=enc.nv, ncl=len(enc.clauses),
             witness=ws.share_exact(enc, sel, M) if sel else None,
             witness2520=ws.share_exact(enc, sel, 2520) if sel else None,
             alpha_check=ws.ShareEncoding.alpha_of(enc, sel) if sel and hasattr(enc, 'qs') else None,
             sel=sorted(sel) if sel else None)
    with open(OUT, 'a') as f:
        f.write(json.dumps(r) + '\n')
    print(kind, ds, 'r', radius, 'T', T, st, 'w', r['witness'], 'w2520', r['witness2520'], f'{sec:.1f}s',
          'nv', enc.nv, 'cl', len(enc.clauses), flush=True)
    return r, enc

if __name__ == '__main__':
    kind, ds, radius = sys.argv[1], tuple(int(x) for x in sys.argv[2].split(',')), int(sys.argv[3])
    T = int(sys.argv[4]) if len(sys.argv) > 4 and sys.argv[4] != '-' else None
    tl = float(sys.argv[5]) if len(sys.argv) > 5 else 300.0
    run(kind, ds, radius, T, tl)
