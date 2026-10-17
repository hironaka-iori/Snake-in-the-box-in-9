import json, glob, math, statistics as st
from collections import defaultdict
W = '/tmp/claude-0/-home-user-Snake-in-the-box-in-9/54df6b79-3551-5be0-97ec-edf141639c5c/scratchpad/wf/'
rows = [json.loads(l) for f in glob.glob(W + 'curve/*.jsonl') for l in open(f) if l.strip()]
by = defaultdict(dict)
for r in rows:
    by[r['entry']][r['keep']] = r
keeps = sorted({r['keep'] for r in rows}, reverse=True)
print('entry  ' + ' '.join('%8d' % k for k in keeps))
for e, d in sorted(by.items()):
    print('%-6s ' % e + ' '.join(('%8.2f' % math.log10(d[k]['mean'])) if k in d else '       -' for k in keeps))
print('rel se max per keep:', {k: round(max(d[k]['se'] / d[k]['mean'] for d in by.values() if k in d), 3) for k in keeps})
print('max_share max per keep:', {k: round(max(d[k]['max_share'] for d in by.values() if k in d), 3) for k in keeps})
# geometric mean across entries and per-8 growth
gm = {}
for k in keeps:
    v = [math.log10(d[k]['mean']) for d in by.values() if k in d]
    if len(v) >= 3:
        gm[k] = (st.mean(v), min(v), max(v), len(v))
print('\nKEEP freed  log10N(geomean) [min,max] n   growth-per-8 (x)')
prev = None
for k in keeps:
    if k not in gm: continue
    m, lo, hi, n = gm[k]
    g = '' if prev is None else '%.1f' % (10 ** ((m - prev[1]) * 8 / (prev[0] - k)))
    print('%4d %5d  %6.2f [%6.2f,%6.2f] %d  %s' % (k, 192 - k, m, lo, hi, n, g))
    prev = (k, m)
