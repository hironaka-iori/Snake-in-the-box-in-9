"""Count LRAT hints before and after backward trimming (keep only lemmas reachable from the empty clause).
usage: python3 lrat_trim_count.py proof.lrat ncls"""
import sys
f, ncls = sys.argv[1], int(sys.argv[2])
hints = {}; last = None
for line in open(f):
    p = line.split()
    if len(p) > 1 and p[1] == 'd':
        continue
    cid = int(p[0]); z = p.index('0', 1)
    hints[cid] = [int(x) for x in p[z + 1:-1]]
    if z == 1: last = cid
need = {last}; stack = [last]; total = sum(len(h) for h in hints.values())
while stack:
    c = stack.pop()
    for h in hints.get(c, ()):
        h = abs(h)
        if h > ncls and h not in need:
            need.add(h); stack.append(h)
kept = sum(len(hints[c]) for c in need)
print(dict(lemmas=len(hints), hints=total, kept_lemmas=len(need), kept_hints=kept))
