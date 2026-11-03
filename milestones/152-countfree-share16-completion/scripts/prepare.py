"""Prepare a guarded full replay and the final actual-snake composition."""
from pathlib import Path
import hashlib,json
H=Path(__file__).resolve().parents[1];R=H.parents[1]
P=R/'milestones/151-countfree-replay-pilot';Q=R/'milestones/150-actual-pair-share'
read=lambda p:json.loads(p.read_text(encoding='utf-8-sig'))
def sha(p):
    d=hashlib.sha256()
    with Path(p).open('rb') as f:
        for b in iter(lambda:f.read(1048576),b''):d.update(b)
    return d.hexdigest()
def write(p,s):
    p.parent.mkdir(parents=True,exist_ok=True);assert not p.exists(),p
    p.write_text(s,encoding='utf-8',newline='\n')
manifest=read(P/'data/file-manifest.json')
for x in manifest['files']:
    path=R/x['path'];assert sha(path)==x['sha256'] and path.stat().st_size==x['bytes'],path
assert read(P/'data/first-group-completion.json')['checked_modules']==49
assert read(P/'data/full-replay-progress.json')['status']=='PASS_BOUNDED_FULL_REPLAY_PREFIX'
assert not (P/'data/full-replay-batch.lock').exists()
plan=read(P/'data/full-execution-plan.json');assert len(plan['module_order'])==342
for a in plan['artifacts']:assert sha(P/a['path'])==a['sha256']
native=read(Q/'replay/data/packed-replay.json');assert native['final_empty']
write(H/'lean/ShareComplete152.lean','''import ShareFromCore150
import ReplayUnsat150

namespace Snake9.ShareTransfer152
open Snake9.LocalWindow Snake9.WindowAutomaton Snake9.DirectionWindow

theorem share16 {m : Nat} (p : Snake m) (r : Nat) (hr : r+6 ≤ m)
    (hshape : canon (dsOf p r 6) = [0,1,2,0,3,2] ∨
      canon (dsOf p r 6).reverse = [0,1,2,0,3,2]) :
    16 ≤ ((List.range 5).map fun i => coreShare 12 p (r+i+1)).sum :=
  Snake9.ShareTransfer150.share16_of_core_unsat Snake9.ReplayFull150.unsat p r hr hshape

#print axioms share16
end Snake9.ShareTransfer152
''')
record=dict(status='PREPARED_FULL_012032_REPLAY_AND_UNCHECKED_FINAL_COMPOSITION',
    source_files_sha256={str(p):sha(p) for p in [Path(__file__),P/'data/file-manifest.json',P/'data/full-execution-plan.json',P/'data/first-group-completion.json',P/'scripts/run_full_replay.py',P/'scripts/check_full_replay.py',Q/'data/semantics-completion.json',Q/'data/ShareFromCore150-audit.json',Q/'lean/ShareFromCore150.lean',H/'lean/ShareComplete152.lean']},
    accepted_prefix_modules=49,total_replay_modules=342,total_segments=878,
    complete_deductions=58182,complete_references=5350080,
    selected='Run the remaining012032 replay alone. Preserve and later resume the same147 coordinator. Audit complete contradiction before compiling the actual-snake composition.',
    full_replay_complete=False,actual_snake_share16_complete=False,new_global_upper_bound=False)
write(H/'data/preparation.json',json.dumps(record,indent=2)+'\n')
print(record['status'])
