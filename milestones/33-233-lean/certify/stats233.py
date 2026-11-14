"""Recompute the certificate figures of the "Unconditional 233" section (read-only).

    nice -n 19 python3 -I milestones/33-233-lean/certify/stats233.py .

Reads only:
  milestones/33-233-lean/certify/data/replay6SB233.jsonl   (one record per generated replay source)
  milestones/33-233-lean/certify/data/prod6SB233.jsonl     (one record per production batch)
  work/final_lean/.lake/guarded_build_233cert.jsonl         (one record per module build)
  work/final_lean/.lake/build/lib/lean/LocalWindow{Cnf,Unsat}/<M>.olean (sizes only)

"seconds" in the guarded-build log is the wall time of each `lean` process (4 or 2 jobs on shared
cores): the same guarded-build wall-time measure that the 235 to 238 write-ups call kernel-hours.

The figures cover the 3,108 certificates whose replay record is in replay6SB233.jsonl (built here).
The 19 certificates built on cloud workers are recorded in data/remotebuild6SB233.jsonl (name, Lean
version, seconds, peak RSS, sha256 of each .olean) and must be added from there.
"""
import collections, json, os, sys

root = sys.argv[1] if len(sys.argv) > 1 else '.'
p = lambda *a: os.path.join(root, *a)
recs = [json.loads(l) for l in open(p('milestones/33-233-lean/certify/data/replay6SB233.jsonl')) if l.strip()]
by = {}
for r in recs:
    by[r['module']] = r          # the last record wins (3 modules were regenerated)
g = [json.loads(l) for l in open(p('work/final_lean/.lake/guarded_build_233cert.jsonl')) if l.strip()]
ok, bad = {}, collections.Counter()
for x in g:
    if x['status'] == 'ok':
        ok[x['module']] = x
    elif x['status'] != 'uptodate':
        bad[(x['module'], x['status'])] += 1
lib = p('work/final_lean/.lake/build/lib/lean')

print('replay records', len(recs), 'unique modules', len(by), dict(collections.Counter(r['kind'] for r in by.values())))
for kind in ('seed', 'share', None):
    rs = [r for r in by.values() if kind is None or r['kind'] == kind]
    built = [r for r in rs if os.path.exists(os.path.join(lib, 'LocalWindowUnsat', r['module'] + '.olean'))]
    out = {'kind': kind or 'all', 'records': len(rs), 'replay_olean_built': len(built),
           'hints_built': sum(r['hints'] for r in built), 'lemmas_built': sum(r['lemmas'] for r in built),
           'max_hints': max((r['hints'] for r in built), default=0),
           'est_hints_built': sum(r['est_hints'] for r in built),
           'source_bytes_built': sum(r['lean_bytes'] for r in built)}
    for d in ('LocalWindowCnf', 'LocalWindowUnsat'):
        fs = [os.path.join(lib, d, r['module'] + '.olean') for r in rs]
        fs = [f for f in fs if os.path.exists(f)]
        secs = [ok[d + '.' + r['module']] for r in rs if d + '.' + r['module'] in ok]
        out[d] = {'olean_files': len(fs), 'olean_bytes': sum(os.path.getsize(f) for f in fs),
                  'build_hours': round(sum(x['seconds'] for x in secs) / 3600, 2),
                  'max_seconds': max((x['seconds'] for x in secs), default=0),
                  'max_rss_gb': max((x['peak_rss_gb'] for x in secs), default=0)}
    print(json.dumps(out))
print('non-ok builds (module, status): count', dict(bad))
other = sorted(m for m in ok if not m.startswith(('LocalWindowCnf.', 'LocalWindowUnsat.')))
print('other modules built in this log', other)
b = [json.loads(l) for l in open(p('milestones/33-233-lean/certify/data/prod6SB233.jsonl')) if l.strip()]
bb = [x for x in b if 'batch' in x]
print('prod batches', len(bb), 'gen_s', sum(x.get('gen_s', 0) for x in bb), 'build_s', sum(x.get('build_s', 0) for x in bb))
