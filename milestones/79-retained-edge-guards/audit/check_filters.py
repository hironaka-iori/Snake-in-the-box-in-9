"""Exhaustively compare finite digit/slice and interval guard conventions."""
from pathlib import Path
import ast,hashlib,json,sys
HERE=Path(__file__).resolve().parents[1];ROOT=HERE.parents[1]
sys.path.insert(0,str(ROOT/'work/solver_packages'))
import numpy as np
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
old=ROOT/'milestones/72-four-count-proof-closure'
audit=json.loads((old/'data/proof-audit.json').read_text())
cases=audit['completed']
src=(HERE/'lean/IntervalCatalogue.lean').read_text()
literal=src.split('def intervalKeys72 : List (List Nat × List (Nat × Nat)) := ',1)[1].split('\n\ntheorem',1)[0]
keys=ast.literal_eval(literal)
assert keys==[(c['dirs'],[tuple(x) for x in c['bounds']]) for c in cases]
codes=np.arange(46656,dtype=np.int64)
C=np.stack([codes//6**j%6+1 for j in range(5,-1,-1)],axis=1)
for j in range(6):assert np.array_equal(codes//6**(5-j)%6+1,C[:,j])
slices=0
for w in range(2,7):
    for s in range(7-w):
        got=codes//6**(6-s-w)%6**w
        expected=np.zeros(len(codes),dtype=np.int64)
        for j in range(s,s+w):expected=expected*6+C[:,j]-1
        assert np.array_equal(got,expected)
        slices+=1
tests=[]
for c in cases:
    for offset in range(2,5):
        for reverse in [False,True]:
            # graph.py's original one-based centre indices.
            indices=[offset+(5-j if reverse else j)-3 for j in range(1,5)]
            original=np.ones(len(codes),dtype=bool)
            for j,(lo,hi) in zip(indices,c['bounds']):
                original&=(C[:,j]>=lo)&(C[:,j]<=hi)
            # IntervalGuards.intervalHit uses s=offset-2 and zero-based i.
            s=offset-2;lean=np.ones(len(codes),dtype=bool)
            for i,(lo,hi) in enumerate(c['bounds']):
                j=s+(4-1-i if reverse else i)
                digit=codes//6**(5-j)%6+1
                lean&=(lo<=digit)&(digit<=hi)
            assert np.array_equal(original,lean)
            tests.append(dict(case=c['case'],offset=offset,reverse=reverse,hits=int(lean.sum())))
# Check every possible internal raw count, not just the bucket representatives.
intervals=sorted(set(tuple(b) for c in cases for b in c['bounds']))
for lo,hi in intervals:
    assert lo<=6 and (hi<6 or hi==21)
    for a in range(1,22):assert (lo<=min(6,a)<=hi)==(lo<=a<=hi)
out=dict(status='PASS_EXHAUSTIVE_COUNT_AND_INTERVAL_CONVENTIONS',codes=46656,
    digit_comparisons=46656*6,slice_offsets=slices,slice_comparisons=46656*slices,
    interval_guard_configurations=len(tests),interval_guard_comparisons=46656*len(tests),
    raw_interval_comparisons=21*len(intervals),cases=[c['case'] for c in cases],tests=tests,
    inputs={p.relative_to(ROOT).as_posix():sha(p) for p in [old/'scripts/graph.py',
        old/'data/proof-audit.json',HERE/'lean/IntervalCatalogue.lean',HERE/'lean/IntervalGuards.lean']},
    scope='Finite convention comparison, distinct from Lean semantics for Python or a full graph rebuild.')
(HERE/'data/filter-comparison.json').write_text(json.dumps(out,indent=2)+'\n')
print(out['status'],out['interval_guard_comparisons'],'interval guard comparisons')
