"""Audit the saved cycle and derive a necessary tradeoff for two share floors."""
from pathlib import Path
from fractions import Fraction as Q
import hashlib, json
H=Path(__file__).resolve().parents[1]; R=H.parents[1]
read=lambda p:json.loads(p.read_text(encoding='utf-8-sig'))
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
source=R/'milestones/144-countfree-share18/data/share18-credit601-over36/results.json'
audit=R/'milestones/144-countfree-share18/data/retuned-review.json'
assert read(audit)['status']=='PASS_BOUNDED_RETUNED_CYCLE_REVIEW'
for p,d in read(audit)['source_files_sha256'].items():
    path=Path(p); assert sha(path if path.is_absolute() else R/path)==d
profile=read(source)['profiles'][0]; cycle=profile['cycle']
assert len(cycle)==14 and all(a['v']==b['u'] for a,b in zip(cycle,cycle[1:]+cycle[:1]))
assert all(not e['occurrence_event'] and not e['shared_bonus'] for e in cycle)

def canon(word):
    seen={}; out=[]
    for d in word:
        if d not in seen:seen[d]=len(seen)
        out.append(seen[d])
    return tuple(out)

def shape(word):return min(canon(word),canon(word[::-1]))

shapes=[shape(e['directions'][-6:]) for e in cycle]
assert (0,1,2,0,3,4) not in shapes
base=[e['weight']//profile['weight_multiplier'] for e in cycle]
assert all(e['weight']%profile['weight_multiplier']==0 for e in cycle)
assert base==[256,246,736,496,371,736,364,496,486,376,736,371,496,724]
fshape=(0,1,2,3,0,1); gshape=(0,1,2,3,4,0)
assert [i for i,s in enumerate(shapes) if s==fshape]==[1,4,8,11]
assert [i for i,s in enumerate(shapes) if s==gshape]==[6,13]

def weights(f,g):
    result=[]
    for e,s,w in zip(cycle,shapes,base):
        floor=f if s==fshape else g if s==gshape else None
        result.append(w if floor is None else max(w,120*e['counts'][-1]+floor))
    return result

rows=[]
for f,g in [(16,4),(19,4),(20,4),(16,11),(16,12),(16,16)]:
    w=weights(f,g)
    expected=[256,240+f,736,496,360+f,736,360+g,496,480+f,376,736,360+f,496,720+g]
    assert w==expected and sum(w)==6848+4*f+2*g and sum(w[:2])==496+f
    mean=Q(sum(w),14)
    # At the cycle mean, all proper cyclic subwalk deficits bound the range.
    deficits=[(k*mean-sum((w+w)[i:i+k]),i,k) for i in range(14) for k in range(1,14)]
    max_deficit=max(t[0] for t in deficits)
    two_edge_deficit=2*mean-496-f
    assert max_deficit==two_edge_deficit
    comparison=(1098960+8*mean+two_edge_deficit)/(4200+mean)
    rows.append(dict(floor_012301=f,floor_012340=g,weights=w,mean=str(mean),
        necessary_range_at_cycle_mean=str(max_deficit),comparison_lower_bound=str(comparison),
        gap_above_235=str(comparison-235),two_edge_range_is_maximum_on_this_cycle=True))
record=dict(status='PASS_EXACT_SAVED_CYCLE_JOINT_FLOOR_AUDIT',cycle_edges=[e['edge'] for e in cycle],
    affine_weight_regime='F >= 11 and G >= 4',cycle_total='6848 + 4F + 2G',
    two_edge_weight='496 + F',necessary_comparison_condition='457F + 225G > 9848 + 7BC',
    comparisons=rows,source_files_sha256={p.relative_to(R).as_posix():sha(p) for p in [Path(__file__),source,audit]},
    scope='Fixed saved graph and other weights; arbitrary 012034 floor and existing uniform occurrence credit leave this cycle unchanged. A necessary condition only, with no global snake bound or sufficient full-graph claim.')
target=H/'data/joint-floor-analysis.json';assert not target.exists()
target.write_text(json.dumps(record,indent=2)+'\n')
print(json.dumps(record))
