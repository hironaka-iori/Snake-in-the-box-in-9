"""Locate pending share targets on the saved four-edge witness only."""
from pathlib import Path
from fractions import Fraction
import hashlib,json
HERE=Path(__file__).resolve().parents[1];ROOT=HERE.parents[1]
read=lambda p:json.loads(p.read_text());sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
graph_path=HERE/'data/graph-audit.json';graph=read(graph_path)
requirements_path=ROOT/'milestones/73-countfree-share-catalogue/data/required-shares.json'
requirements=read(requirements_path)['requirements']
targets={tuple(r['shape']):r for r in requirements}
def canon(word):
    d={};return tuple(d.setdefault(x,len(d)) for x in word)
rows=[]
for row in graph['cycle']:
    word=row['directions'][-6:];shape=min(canon(word),canon(word[::-1]));target=targets[shape]
    base=120*row['counts'][-1];new=max(row['weight'],base+target['selected_share'])
    rows.append(dict(edge=row['edge'],shape=list(shape),case=target['case_number'],
        current_credit=row['weight']-base,target_floor=target['selected_share'],
        old_weight=row['weight'],hypothetical_weight=new,increase=new-row['weight']))
affected=sorted({r['case'] for r in rows if r['increase']})
assert affected==[7302,7307]
total=sum(r['hypothetical_weight'] for r in rows);assert total==1988
out=dict(status='CONDITIONAL_WITNESS_SENSITIVITY_ONLY',rows=rows,affected_pending_cases=affected,
    current_cycle_mean='483',hypothetical_cycle_mean=str(Fraction(total,4)),
    input_sha256={p.relative_to(ROOT).as_posix():sha(p) for p in [Path(__file__),graph_path,requirements_path]},
    scope='Applying the two unproved target floors raises this saved cycle to 497. No new complete-graph mean or global bound is inferred; other critical cycles may remain.')
(HERE/'data/target-sensitivity.json').write_text(json.dumps(out,indent=2)+'\n')
print(out['status'],affected,'saved cycle 483 ->',out['hypothetical_cycle_mean'])
