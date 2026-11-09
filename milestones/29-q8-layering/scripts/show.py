import json,sys
for l in open(sys.argv[1]):
    r=json.loads(l); print(r['c'], r['g_le'], r.get('g_eq'), r.get('g3_short2'), r.get('g3_short1'), r.get('g3_short0'), r.get('wit_le_paths'), [x for x in r['log_le']])
