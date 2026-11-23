#!/usr/bin/env python3
"""meas.py LABEL LOG -- cmd ...   run cmd, append a JSON line {label, cmd, rc, wall_s, peak_rss_mb} to LOG"""
import sys, subprocess, time, resource, json
lab, log = sys.argv[1], sys.argv[2]; cmd = sys.argv[sys.argv.index('--') + 1:]
t = time.time(); r = subprocess.run(cmd); w = time.time() - t
ru = resource.getrusage(resource.RUSAGE_CHILDREN)
rec = dict(label=lab, cmd=' '.join(cmd), rc=r.returncode, wall_s=round(w, 2), peak_rss_mb=round(ru.ru_maxrss / 1024), utc=time.strftime('%H:%M:%SZ', time.gmtime()))
open(log, 'a').write(json.dumps(rec) + '\n'); print(json.dumps(rec), file=sys.stderr)
