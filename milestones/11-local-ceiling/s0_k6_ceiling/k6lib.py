"""Windows of the period-3 all-alpha=4 ceiling cycle, extended to k = 5, 6, 7 (and longer)."""
import sys, os, json, time
sys.dont_write_bytecode = True
R = os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', '..')
sys.path.insert(0, R + '/11-local-ceiling/s0_share_loop'); sys.path.insert(0, R + '/10-window-aggregate/scripts')
import wincert, wincert_share as ws
from refine import canon, induced, key

def nseq(N):
    """Direction sequence of the cycle lift: blocks (N[j+1], N[j], N[j-1])."""
    ds = []
    for j in range(1, len(N) - 1):
        ds += [N[j + 1], N[j], N[j - 1]]
    return ds

def windows(N, k):
    """All k-centre windows (k+1 directions) of the lift, canonical keys with phase."""
    ds = nseq(N); out = {}
    for i in range(len(ds) - k):
        sub = tuple(ds[i:i + k + 1])
        if not induced(sub):
            out.setdefault(('NOT_INDUCED', canon(sub)), i % 3); continue
        kk = key(sub, (4,) * k)
        out.setdefault(kk, i % 3)
    return out

if __name__ == '__main__':
    gen = list(range(9)) * 4           # N_j = j mod 9  (fresh direction each new step)
    p5 = list(range(5)) * 7            # N_j = j mod 5  (x = p choice: N_{j+1} = N_{j-4})
    for name, N in (('fresh9', gen), ('period5', p5), ('period6', list(range(6)) * 6), ('period7', list(range(7)) * 5)):
        print(name, 'induced overall prefix:', max(L for L in range(4, len(nseq(N)) + 1) if induced(tuple(nseq(N)[:L]))))
        for k in (5, 6, 7, 8):
            print('  k', k, [(kk[0], ph) for kk, ph in windows(N, k).items()])
