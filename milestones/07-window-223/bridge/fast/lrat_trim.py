"""Backward-trim an LRAT proof (keep steps reachable from the empty clause), drop deletions,
renumber nothing. usage: lrat_trim.py CNF IN OUT"""
import sys
cnf, inp, out = sys.argv[1:4]
ncl = sum(1 for l in open(cnf) if l[0] not in 'pc\n')
steps = {}
order = []
for line in open(inp):
    t = line.split()
    if not t or t[1] == 'd': continue
    xs = list(map(int, t)); z = xs.index(0, 1)
    sid = xs[0]; steps[sid] = (xs[1:z], xs[z+1:-1]); order.append(sid)
    if z == 1: last = sid; break
need = {last}; stack = [last]
while stack:
    s = stack.pop()
    for h in steps[s][1]:
        assert h > 0, 'RAT hint'
        if h > ncl and h not in need: need.add(h); stack.append(h)
H = 0; n = 0
with open(out, 'w') as f:
    for sid in order:
        if sid in need:
            c, hs = steps[sid]; H += len(hs); n += 1
            f.write(f"{sid} {' '.join(map(str, c))} 0 {' '.join(map(str, hs))} 0\n")
print(f'steps {n} hints {H}')
