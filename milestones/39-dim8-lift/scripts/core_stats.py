"""Core statistics of an LRAT refutation: input clauses reachable from the empty clause, and the
distinct variables they use.  usage: python3 core_stats.py f.cnf f.lrat"""
import sys
cnf, lrat = sys.argv[1], sys.argv[2]
ncls = int(open(cnf).readline().split()[3])
hints = {}; last = None
for line in open(lrat):
    p = line.split()
    if len(p) > 1 and p[1] == 'd': continue
    cid = int(p[0]); z = p.index('0', 1)
    hints[cid] = [abs(int(x)) for x in p[z + 1:-1]]
    if z == 1: last = cid
need = set(); core = set(); st = [last]
while st:
    c = st.pop()
    for h in hints.get(c, ()):
        if h <= ncls: core.add(h)
        elif h not in need: need.add(h); st.append(h)
vs = set(); i = 0
for line in open(cnf):
    if line.startswith('p'): continue
    i += 1
    if i in core: vs.update(abs(int(x)) for x in line.split()[:-1])
print(dict(inputs=ncls, core_clauses=len(core), core_vars=len(vs), lemmas_kept=len(need), max_var=max(vs)))
