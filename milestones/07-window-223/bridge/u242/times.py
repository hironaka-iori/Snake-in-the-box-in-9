"""Summarise out/times.log by group (per window case, generic, final)."""
import re, sys, collections
g = collections.OrderedDict(); last = {}
for l in open(sys.argv[1]):
    m = re.match(r'(\S+) rc=(\d+) ([\d.]+) s peak (\d+) KB \(anon (\d+) KB\)', l)
    if not m: continue
    mod, rc, t, pk, an = m.group(1), int(m.group(2)), float(m.group(3)), int(m.group(4)), int(m.group(5))
    last[mod] = (t, pk, an)
for mod, (t, pk, an) in last.items():
    k = re.match(r'(W\d+\w*?(Rep|Dis|A|B|C))(Inputs|S\d+|Main|G1.*)$', mod)
    key = (k.group(1) + (' G2' if not k.group(3).startswith('G1') else ' G1')) if k else mod
    a = g.setdefault(key, [0, 0.0, 0])
    a[0] += 1; a[1] += t; a[2] = max(a[2], an)
tot = 0
for k, (n, t, an) in g.items():
    tot += t; print(f'{k:16s} {n:3d} modules {t:8.1f} s  max anon {an/1e6:.2f} GB')
print(f'total {sum(v[0] for v in g.values())} modules {tot:.1f} s')
