"""Check coverage of every Q8 projection from the frozen high-dimensional sections."""
import gzip
import json
from collections import Counter
from certify_q9_projection_bound import projected_set
from verify_q9_center_avoidance import verify

def rows(f):
    return [json.loads(row) for row in open(f)]
def mask(s):
    return sum(1<<v for v in s)
docs=gzip.open('q9_high_section_surgery_20261120/sections.gz','rt')
paths=[list(map(int,row.split()))[3:] for row in docs]
expected={mask(projected_set(path,d)) for path in paths for d in range(9)}
read={}
out={}
for f in ('q9_sections_unordered_projection.jsonl','q9_sections_unordered_remainder.jsonl'):
    for i,d,st,w in rows(f):
        if i=='control':verify(w);assert len(w)==192;continue
        key=mask(projected_set(paths[i],d));assert key not in out
        read[i,d]=key;out[key]=st
assert set(out)==expected
for f in ('q9_sections_unordered_retry_a.jsonl','q9_sections_unordered_retry_b.jsonl','q9_sections_unordered_retry_last.jsonl'):
    for i,d,st,w in rows(f):
        key=read[i,d];assert out[key]=='UNKNOWN';out[key]=st
assert set(out.values())=={'PROJECTION','SIZE','UNSAT'}
print(json.dumps(dict(source_sections=len(paths),distinct_column_sets=len(expected),status=Counter(out.values()))))
