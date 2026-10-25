import json, sys, time
from shapes import unroll, rules_of_cycle
cyc = json.load(open('data/cycles.json'))
lim = int(sys.argv[1])
for name, c in cyc.items():
    st = [tuple(s) for s in c['states']]
    r = [unroll(st, ph, limit=lim) for ph in range(len(st))]
    print(f"{name:26s} p={len(st):2d} rules={rules_of_cycle(st)} L={[x['max_transitions'] for x in r]} exh={[x['exhaustive'] for x in r].count(True)}/{len(st)}", flush=True)
