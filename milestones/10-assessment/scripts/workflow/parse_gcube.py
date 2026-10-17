import json, re, sys
from collections import Counter
for fn in sys.argv[1:]:
    r = []
    for l in open(fn):
        l = re.sub(r'"wall":\.', '"wall":0.', l.strip())
        if l: r.append(json.loads(l))
    secs = [x.get('seconds', x.get('wall', 0)) for x in r]
    print(fn.split('/')[-1], len(r), dict(Counter(x['status'] for x in r)), 'solver_s sum %.2f mean %.3f max %.2f' % (sum(secs), sum(secs) / len(secs), max(secs)),
          'conflicts sum', sum((x.get('conflicts') or 0) for x in r), 'cycle cuts', sum(x.get('cycle_cuts', 0) for x in r))
