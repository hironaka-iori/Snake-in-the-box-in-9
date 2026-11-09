"""Exact h_{n,k}(c) (largest max-degree-2 set with <= c paths and no cycle inside a k-subcube)
for small n by fakesat.run; writes ../data/fake_table.jsonl."""
import sys, json, os
from fakesat import run
n, k = int(sys.argv[1]), int(sys.argv[2])
out = open(os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'data', 'fake_table.jsonl'), 'a')
for c in range(0, 2 ** (n - 3) + 1):
    L = max(4 * c + 1, 2 ** (n - 1) - 2 ** (n - 3))
    best = None
    while True:
        st, sel, r, t = run(n, c, L, k, 600, verbose=False)
        if st != 'SAT':
            break
        best = (len(sel), sel)
        L = len(sel) + 1
    rec = dict(n=n, k=k, c=c, h=best[0] if best else None, proved_upper=L - 1 if st == 'UNSAT' else None,
               last=st, time=round(t, 1), witness=best[1] if best else None,
               note='h >= every value tried below; search starts at L = max(4c+1, 3*2^(n-3))')
    print(n, k, c, rec['h'], st, rec['time'], flush=True)
    out.write(json.dumps(rec) + '\n')
