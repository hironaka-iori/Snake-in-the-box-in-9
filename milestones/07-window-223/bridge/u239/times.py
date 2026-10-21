"""Summarise a compile-time log (`Mod rc=0 SECONDS s peak KB (anon KB)` lines, last entry per module)
of the 239 build: totals per module kind, the largest modules, and G2 cost per window against the
RUP steps and hints of its proof (WORK/data/*.info.json, WORK/sym/*.json from regen.py --keep, or
none).  usage: python3 -I times.py TIMES.LOG [WORK]"""
import collections, json, os, re, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from gen import CASES_JSON, modname

last = {}
for l in open(sys.argv[1]):
    m = re.match(r'(\S+) rc=0 ([\d.]+) s peak (\d+) KB \(anon (\d+) KB\)', l)
    if m:
        last[m.group(1)] = (float(m.group(2)), int(m.group(3)), int(m.group(4)))
order = open(os.path.join(os.path.dirname(os.path.abspath(__file__)), 'build_order.txt')).read().split()
kind = collections.defaultdict(lambda: [0, 0.0, 0])
for mod in order:
    if mod not in last: continue
    t, pk, an = last[mod]
    k = re.sub(r'^DV\d+(?:_[\dL]+)+', '', mod)
    k = re.sub(r'(S|G1C|InputsD)\d+$', r'\1', k)
    a = kind[k]; a[0] += 1; a[1] += t; a[2] = max(a[2], an)
tot = sum(v[1] for v in kind.values())
for k, (n, t, an) in sorted(kind.items(), key=lambda x: -x[1][1]):
    print(f'{k:12s} {n:5d} modules {t:9.1f} s  max anon {an / 1e6:.2f} GB')
print(f'total {sum(v[0] for v in kind.values())} modules {tot:.1f} s ({tot / 3600:.2f} h)')
print('largest modules:')
for mod in sorted(last, key=lambda m: -last[m][0])[:12]:
    print(f'  {mod:28s} {last[mod][0]:7.1f} s  anon {last[mod][2] / 1e6:.2f} GB')
work = sys.argv[2] if len(sys.argv) > 2 else None
rows = []
for c in CASES_JSON:
    if c['kind'] == 'reuse': continue
    m = modname(c['tag'])
    g2 = sum(last[x][0] for x in order if x in last and re.fullmatch(m + r'(Inputs\w*|S\d+|Main)', x))
    g1 = sum(last[x][0] for x in order if x in last and re.fullmatch(m + r'G1\w*', x))
    st = h = None
    if work:
        for p in (f'{work}/data/{c["tag"]}.info.json', f'{work}/sym/{c["tag"]}.json'):
            if os.path.exists(p):
                j = json.load(open(p)); st, h = j['steps'], j['hints']
    rows.append((g2, g1, c['tag'], c['kind'], st, h))
rows.sort(reverse=True)
print('per window (G2 s, G1 s, steps, hints), most expensive first:')
for g2, g1, t, k, st, h in rows[:15]:
    print(f'  {t:22s} {k:4s} G2 {g2:7.1f} s  G1 {g1:6.1f} s  steps {st}  hints {h}')
for k in ('trim', 'sym'):
    r = [x for x in rows if x[3] == k]
    print(f'{k}: {len(r)} windows, G2 {sum(x[0] for x in r):.0f} s, G1 {sum(x[1] for x in r):.0f} s'
          + (f', {sum(x[4] for x in r)} steps, {sum(x[5] for x in r)} hints' if work and all(x[4] for x in r) else ''))
if work and all(x[4] for x in rows):
    H = sum(x[5] for x in rows); G = sum(x[0] for x in rows)
    print(f'G2 rate: {H / G:.0f} hints per second, {sum(x[4] for x in rows) / G:.0f} steps per second')
