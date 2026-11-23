#!/usr/bin/env python3
"""mkchild.py PARENT.cnf OUT.cnf LIT  -> OUT = PARENT plus the unit clause LIT (header clause count +1); verifies and prints JSON"""
import sys, time, hashlib, json, os
p, o, lit = sys.argv[1], sys.argv[2], int(sys.argv[3])
t = time.time(); data = open(p, 'rb').read(); tr = time.time() - t
hdr, body = data.split(b'\n', 1); _, _, nv, nc = hdr.split(); nv, nc = int(nv), int(nc)
assert 0 < abs(lit) <= nv
t = time.time()
with open(o + '.tmp', 'wb') as f:
    f.write(b'p cnf %d %d\n' % (nv, nc + 1)); f.write(body); f.write(b'%d 0\n' % lit); f.flush(); os.fsync(f.fileno())
os.rename(o + '.tmp', o); tw = time.time() - t
# verify: same var count, clause count +1, body identical, last line is the unit
d2 = open(o, 'rb').read(); h2, b2 = d2.split(b'\n', 1)
assert h2 == b'p cnf %d %d' % (nv, nc + 1) and b2[:len(body)] == body and b2[len(body):] == b'%d 0\n' % lit
assert b2.count(b' 0\n') + (1 if b2.startswith(b'0\n') else 0) >= nc + 1
print(json.dumps(dict(child=o, lit=lit, header='p cnf %d %d' % (nv, nc + 1), sha256=hashlib.sha256(d2).hexdigest(),
                      parent_sha256=hashlib.sha256(data).hexdigest(), read_s=round(tr, 3), write_s=round(tw, 3),
                      on_disk_utc=time.strftime('%H:%M:%SZ', time.gmtime(os.path.getmtime(o))))))
