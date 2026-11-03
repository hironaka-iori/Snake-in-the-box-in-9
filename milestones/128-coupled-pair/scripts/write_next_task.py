"""Save an exhaustive next case split without claiming that either case is solved."""
from pathlib import Path
import hashlib,json
H=Path(__file__).resolve().parents[1];R=H.parents[1]
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
names=['milestones/125-critical-six-count/lean/ActualBounds125.lean',
 'milestones/125-critical-six-count/data/ActualBounds125-audit.json',
 'milestones/121-replacement-window-pressure/lean/ActualPair121.lean',
 'milestones/121-replacement-window-pressure/data/ActualPair121-audit.json',
 'milestones/128-coupled-pair/lean/PairLower128.lean',
 'milestones/128-coupled-pair/data/preparation.json',
 'milestones/128-coupled-pair/work/pair.cnf']
out=dict(status='PROPOSED_EXHAUSTIVE_SPLIT_NOT_ENCODED_OR_SEARCHED',pattern='0120324',sum_cap=22,
 branches=[dict(fourth_count=3,necessary_intervals=[[3,21],[5,21],[1,21],[3,3],[1,21],[1,21]],
                other_positions=[3,5,6],other_sum_upper=11),
           dict(fourth_count_lower=4,necessary_intervals=[[1,21],[2,21],[1,21],[4,21],[1,21],[1,21]])],
 proof_obligations=[
 'Use actual_six_bounds under the total22 hypothesis to obtain fourth count at least3.',
 'Split into fourth count3 and fourth count at least4; both cases are required.',
 'In the first case actual_pair_sum gives second count at least5.',
 'In the first case first_fourth_exclusion gives first count at least3.',
 'Subtract these lower counts and the fourth count3 from the total22 to get the other three counts at most11.',
 'Check this arithmetic for actual snakes in Lean before using new branch constraints in a final exclusion.',
 'Retain the combined six-count target and the checked paired constraint; do not narrow the claim to only one branch.',
 'A complete native result requires proof replay and full actual-snake transfer.'],
 source_pins={name:sha(R/name) for name in names},script_sha256=sha(Path(__file__)),
 scope='Written arithmetic consequences of checked premises and a proposed next search. No branch is excluded, and the new split assembly has not been checked in Lean.')
p=H/'data/next-case-task.json';assert not p.exists()
p.write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')
print(json.dumps({k:v for k,v in out.items() if k not in ['source_pins','proof_obligations']},indent=2))
