"""Exact saved-cycle and subwalk arithmetic; no global graph search."""
from fractions import Fraction as F
from pathlib import Path
import hashlib,json
H=Path(__file__).resolve().parents[1];R=H.parents[1]
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
paths=[R/'milestones/142-retuned-occurrence-credit/data/credit533-over12/results.json',R/'milestones/142-retuned-occurrence-credit/data/share-targets.json',Path(__file__)]
cycle=json.loads(paths[0].read_text())['profiles'][0]['cycle']
assert len(cycle)==9 and all(e['v']==cycle[(i+1)%9]['u'] for i,e in enumerate(cycle))
assert not any(e['occurrence_event'] or e['shared_bonus'] for e in cycle)
def canon(ds):
 names={};return tuple(names.setdefault(x,len(names)) for x in ds)
def shape(ds):return min(canon(ds),canon(ds[::-1]))
affected=[i for i,e in enumerate(cycle) if shape(e['directions'][-6:])==(0,1,2,0,3,4)]
assert affected==[0,1,3,4,6,7]
rows=[]
for h in range(21):
 weights=[max(e['base_weight'],120*e['counts'][-1]+h) if i in affected else e['base_weight'] for i,e in enumerate(cycle)]
 mean=F(sum(weights),9);a=weights+weights
 choices=[(k*mean-sum(a[i:i+k]),i,k,sum(a[i:i+k])) for i in range(9) for k in range(10)]
 ran,start,length,total=max(choices)
 comparison=(1098960+8*mean+ran)/(4200+mean)
 rows.append(dict(floor=h,weights=weights,total_weight=sum(weights),mean=str(mean),minimum_cycle_only_range_at_mean=str(ran),max_deficit_walk_start=start,walk_length=length,walk_weight=total,comparison_at_cycle_mean=str(comparison),gap_from235=str(comparison-235)))
assert rows[14]['weights']==[614,494,376,734,374,492,614,374,376]
assert rows[14]['walk_length']==5 and rows[14]['max_deficit_walk_start']==4 and rows[14]['walk_weight']==2230
assert all(F(x['gap_from235'])>0 for x in rows[:15]) and F(rows[15]['gap_from235'])<0
# For all lower floors, every cycle and subwalk weight is bounded by floor14's.
assert all(all(a<=b for a,b in zip(x['weights'],rows[14]['weights'])) for x in rows[:15])
j=dict(status='PASS_EXACT_CYCLE_AND_SUBWALK_ARITHMETIC',source_files_sha256={p.relative_to(R).as_posix():sha(p) for p in paths},cycle_edges=[e['edge'] for e in cycle],cycle_adjacency_verified=True,all_cycle_events_zero=True,affected_rows=affected,rows=rows,obstruction=dict(floors='Any floor at most14, keeping all other graph rules fixed.',cycle_mean_cap='4448/9',walk_edge_indices=[4,5,6,7,8],walk_weight_upper_bound=2230,range_lower_bound='5*mu-2230',universal_comparison_lower_bound='4964197/21124',gap_from235='57/21124'),selected_next_target=18,next_target_reason='Floor15 is first not excluded by this saved cycle and walk. Floor18 is the existing additional-profile requirement, so target it directly instead of certifying another merely necessary threshold.',scope='Exact local graph witnesses only; no full graph optimisation, actual-snake theorem, or global upper bound. The cycle-only range at its mean does not claim an optimal full-graph range.')
(H/'data/range-analysis.json').write_text(json.dumps(j,indent=2)+'\n',encoding='utf-8')
print(json.dumps(dict(status=j['status'],obstruction=j['obstruction'],selected_next_target=18)))
