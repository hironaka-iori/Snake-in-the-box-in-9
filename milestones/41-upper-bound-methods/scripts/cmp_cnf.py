import os, sys, json, time
HERE = os.path.dirname(os.path.abspath(__file__)); MS = os.path.abspath(os.path.join(HERE, '..', '..'))
for p in ('38-220-conditional/trackA', '28-combined-identities', '11-local-ceiling/s0_share_loop', '10-window-aggregate/scripts'):
    sys.path.insert(0, os.path.join(MS, p))
from enc2 import AltShare
from tier7 import ws, window_from_dirs
import binsolve
dirs, T, tl = json.loads(sys.argv[1]), int(sys.argv[2]), float(sys.argv[3])
enc = AltShare(window_from_dirs(dirs), ws.alpha_arg([(1, 21)] * 7), 4, 12, T - 1, 'merge', True, 1)
print(json.dumps(dict(dirs=dirs, T=T, cadical=binsolve.solve(enc, (), tl))), flush=True)
