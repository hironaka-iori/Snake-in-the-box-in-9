"""Measure which already proposed catalogue floors affect the saved cycles."""
from pathlib import Path
from fractions import Fraction as F
import hashlib,json
H=Path(__file__).resolve().parents[1];R=H.parents[1]
read=lambda p:json.loads(Path(p).read_text(encoding='utf-8-sig'))
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
def canon(xs):
 d={};a=[]
 for x in xs:
  if x not in d:d[x]=len(d)
  a.append(d[x])
 return tuple(a)
def shape(xs):return min(canon(xs),canon(xs[::-1]))
files=[H/'data/share18-impact/results.json',H/'data/share18-credit601-over36/results.json']
out=[]
for file,targets in zip(files,[[((0,1,2,0,3,2),16)],[((0,1,2,3,0,1),16),((0,1,2,3,4,0),16)]]):
 p=read(file)['profiles'][0];cy=p['cycle'];factor=p['weight_multiplier']
 assert all(not q['shared_bonus'] for q in cy)
 # Remove the coefficient only where it was actually applied.
 ws=[F(q['weight']-q['occurrence_credit_scaled']*q['occurrence_event'],factor) for q in cy]
 assert all(w.denominator==1 for w in ws)
 entries=[];combined=ws.copy()
 for target,floor in targets:
  gains=[max(0,120*q['counts'][-1]+floor-int(w)) if shape(q['directions'][-6:])==target else 0 for q,w in zip(cy,ws)]
  entries.append(dict(shape=''.join(map(str,target)),floor=floor,gains=gains,total_gain=sum(gains),mean_if_added_alone=str((sum(ws)+sum(gains))/len(ws))))
  combined=[w+g for w,g in zip(combined,gains)]
 assert sum(combined)/len(combined)==496
 out.append(dict(cycle_length=len(cy),baseline_mean=str(sum(ws)/len(ws)),targets=entries,
  combined_mean='496',combined_total=str(sum(combined)),scope='Only these saved cycles, not sufficiency on the full graph.'))
j=dict(status='PASS_EXACT_SAVED_CYCLE_TARGET_COMPARISON',cycles=out,
 selected_next_shape='012301',selected_floor=16,resolution=12,broad_count_intervals=[[0,21]]*5,
 reason='The surviving14-cycle gains30 from012301 floor16 and24 from012340 floor16. Select012301 first; both are needed to bring this cycle to mean496 under the existing target floors. The separate11-cycle still requires012032 floor16 or another valid change.',
 actual_theorem_complete=False,existing_case_label=7303,case_directory_present=(R/'milestones/73-countfree-share-catalogue/cases/case7303').exists(),
 next_actions=['Locate and validate the saved012301 native refutation before generating any new query.','Check exact saved-cycle and full-graph impact before committing to a large replay.','For replay, complete the literal-initial-tree validity proof; do not reuse a prefix receipt as a local snake theorem.'],
 source_files_sha256={str(p.relative_to(R)):sha(p) for p in [Path(__file__),*files,H/'data/retuned-review.json']})
(H/'data/next-task.json').write_text(json.dumps(j,indent=2)+'\n');print(json.dumps(j))
