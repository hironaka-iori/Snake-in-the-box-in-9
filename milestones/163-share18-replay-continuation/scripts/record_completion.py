"""Record the accepted bounded continuation and its remaining obligations."""
from pathlib import Path
import hashlib,json
H=Path(__file__).resolve().parents[1];R=H.parents[1]

def main():
    q=json.loads((H/'data/completion.json').read_text())
    assert q['status']=='PASS_BOUNDED_PREFIX_COMPOSITION'
    assert q['original_CNF_implies_prefix_checkpoint_truth']
    assert not q['full_share18_replay_complete'] and not q['new_global_bound']
    assert not (R/'milestones/161-share18-full-replay/data/replay-batch.lock').exists()
    for path,expected in [
        (R/'.gitignore','20d6df071a62fabfd98360ddf985088445fde2dec19ef0281f5ab5c6d2b1941b'),
        (R/'milestones/50-three-count-return/excess-screen/data/critical-family.json','466e23170f15072cae3643971b5d9a62b2227fc9ffb4bca276173dc19892db82'),
        (R/'paper/snake9_research.tex','e46822ed639866f4c188328712c0d5212dc84887c26d52d4f491cd356f18afdb'),
        (Path('D:/Codex/2026-10-13/new-chat/outputs/snake9_research.tex'),'e46822ed639866f4c188328712c0d5212dc84887c26d52d4f491cd356f18afdb')]:
        assert hashlib.sha256(path.read_bytes()).hexdigest()==expected,str(path)
    header=f'''# Current result: extended share-18 proof checkpoint

Milestones 161 and 163 now connect {q['completed_segments']:,} continuation segments in
{q['completed_groups']} complete groups to the original clause set through a Lean-checked
consequence theorem. Including the earlier prefix, this covers
{q['total_checked_deductions']:,} deductions and {q['total_checked_references']:,} references.
There remain {q['remaining_deductions']:,} deductions and {q['remaining_references']:,} references.

Read milestones/163-share18-replay-continuation/COMPLETION.md and its adjacent
data/completion.json. Continue the existing161 replay in bounded batches,
reusing accepted modules. Its sources and execution plan are unchanged.
Historical publication manifests refer to their recorded commits; do not
expect their old progress-file hashes to match a later continuation.

The final geometry and reversal sources are compatible with the accepted
encoding and can be reused unchanged after the full contradiction passes.
The refutation wrapper must then consume that completed contradiction.
These final checks are still pending. The universal012034 share-18 theorem
and a new global upper bound are not established.

Last full paper revision:156; next:166. Historical updates follow.

'''
    for rel in ['README.md','handoff/CURRENT_STATUS.md','handoff/NEXT_AGENT_PROMPT.md']:
        p=R/rel;old=p.read_bytes()
        if not old.startswith(header.encode()):p.write_bytes(header.encode()+old)
    body=header.split('Last full paper revision:')[0].replace(
        '# Current result: extended share-18 proof checkpoint','# Milestone163: accepted continuation and final-transfer plan')
    body+='''The bounded consequence theorem was checked after the group audit. Its
only hypothesis is satisfaction of the original exported clause set; its
conclusion is truth of the saved checkpoint after the completed groups.
It does not assert that this clause set is satisfiable, and it does not yet
derive the final empty clause.

The source review in ../162-share18-composition-plan/review/remaining-composition.md identifies three final
checks after the complete replay: refutation assembly, coordinate-labelled
geometry, and reversal. The last two original sources can be reused
byte-for-byte. This compatibility assessment is independent of the completed
bounded consequence and does not substitute for their future Lean checks.

Resume the existing161 driver with the configured Python runtime. Inspect
data/replay-progress.json and confirm that no batch is active first. The
driver verifies and reuses accepted modules and stops at the first failure.
Keep the checked object, source and log bytes unchanged. No new Boolean
solver query or additional mathematical definition is required.

The old161 pilot audit and publication manifests describe their historical
acceptance state. Later progress overwrites only the current progress file;
the original batch logs and accepted receipts remain preserved. Use the
latest bounded-group audit and this completion record for the extended state.
'''
    (H/'COMPLETION.md').write_text(body,encoding='utf-8')
    (H/'README.md').write_text('# Milestone163\n\nRead COMPLETION.md for the checked bounded continuation and ../162-share18-composition-plan/review/remaining-composition.md for the remaining actual-snake proof. The full contradiction and local share18 theorem remain pending.\n',encoding='utf-8')
    print('RECORDED_ACCEPTED_CONTINUATION',q['total_checked_deductions'])

if __name__=='__main__':main()
