"""Select the next conditional graph experiment from the surviving saved cycle."""
from pathlib import Path
from fractions import Fraction
import hashlib,json
H=Path(__file__).resolve().parents[1];R=H.parents[1]
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
source=R/'milestones/124-six-count-cycle-pressure/data/graph-26-25-25/cycle-targets.json'
j=json.loads(source.read_text());profile=next(x for x in j['profiles'] if x['profile']=='completed')
edges=profile['edges'];assert len(edges)==18 and profile['source_mean']=='2915/6'
rows=[]
for word in sorted({e['canonical_shape'] for e in edges}):
 selected=[]
 for e in edges:
  if e['canonical_shape']!=word:continue
  proposed=24*max(0,25-e['six_sum']) if e['chronological_first_symbol_exact'] else 0
  gain=max(e['old_bonus24'],proposed)-e['old_bonus24']
  selected.append(dict(edge=e['edge'],counts=e['chronological_counts'],sum=e['six_sum'],
                       first_symbol_exact=e['chronological_first_symbol_exact'],extra_credit=gain))
 gain=sum(x['extra_credit'] for x in selected)
 rows.append(dict(shape=word,occurrences=len(selected),extra_cycle_weight=gain,
                  hypothetical_saved_cycle_mean=str(Fraction(profile['source_mean'])+Fraction(gain,len(edges))),edges=selected))
choice=max(rows,key=lambda x:x['extra_cycle_weight']);assert choice['shape']=='0123104' and choice['extra_cycle_weight']==288
probe=R/'milestones/124-six-count-cycle-pressure/data/probes/0123104-universal-total24-resume.json'
p=json.loads(probe.read_text());assert p['status']=='UNSAT_UNCERTIFIED' and p['directions']==[0,1,2,3,1,0,4]
pins=[source,probe,H/'data/odd-pair-verification.json',H/'data/odd-cycle-review.json',
      R/'milestones/121-replacement-window-pressure/data/pair-graph/results.json']
record=dict(status='PROPOSED_FULL_GRAPH_TEST_NOT_EXECUTED',candidate_shape='0123104',candidate_six_count_floor=25,
 odd_length_pair_floor=9,odd_length_pair_floor_scope='Proved for actual odd-length snakes; the proposed exclusion target is length235.',
 candidate_native_status='UNSAT_UNCERTIFIED',candidate_lean_proof_complete=False,
 saved_cycle_comparisons=rows,selected_hypothetical_cycle_mean=choice['hypothetical_saved_cycle_mean'],
 next_action='Evaluate both saved graph profiles with the proved odd-length pair floor9 and the still-unproved six-count floor25 on0123104. Check all retained-edge inequalities and new attaining cycles. Only pursue a new local certificate if the full graph experiment supports the expected numerical improvement.',
 scope='These are recalculated weights of one saved18-edge witness under hypothetical local floors, not new global minimum means or snake bounds. Symbol6 retains its full interval; credit uses the exact first-symbol guard and the maximum of competing bonuses. Existing unproved graph hypotheses remain unproved.',
 source_pins={x.relative_to(R).as_posix():sha(x) for x in pins},script_sha256=sha(Path(__file__)))
out=H/'data/next-pressure-task.json';assert not out.exists();out.write_text(json.dumps(record,indent=2)+'\n',encoding='utf-8')
print(json.dumps(dict(choice=choice['shape'],extra_saved_cycle_weight=choice['extra_cycle_weight'],hypothetical_saved_cycle_mean=choice['hypothetical_saved_cycle_mean'],full_graph_experiment_run=False)))
