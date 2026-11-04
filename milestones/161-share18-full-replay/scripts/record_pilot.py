"""Record the accepted pilot without claiming the remaining proof is complete."""
from pathlib import Path
import hashlib
import json

H = Path(__file__).resolve().parents[1]
R = H.parents[1]

def main():
    q = json.loads((H / 'data/pilot-completion.json').read_text())
    assert q['status'] == 'PASS_FIRST32_REMAINING_SEGMENTS'
    assert not q['full_share18_replay_complete'] and not q['new_global_bound']
    assert not (H / 'data/replay-batch.lock').exists()
    for path, expected in [
        (R / '.gitignore', '20d6df071a62fabfd98360ddf985088445fde2dec19ef0281f5ab5c6d2b1941b'),
        (R / 'milestones/50-three-count-return/excess-screen/data/critical-family.json', '466e23170f15072cae3643971b5d9a62b2227fc9ffb4bca276173dc19892db82'),
        (R / 'paper/snake9_research.tex', 'e46822ed639866f4c188328712c0d5212dc84887c26d52d4f491cd356f18afdb'),
        (Path('D:/Codex/2026-10-13/new-chat/outputs/snake9_research.tex'), 'e46822ed639866f4c188328712c0d5212dc84887c26d52d4f491cd356f18afdb')]:
        assert hashlib.sha256(path.read_bytes()).hexdigest() == expected, str(path)
    header = f'''# Current result: first continuation group checked in Lean

Milestone 161 passed its twelve-module pilot: 32 continuation segments,
{q['newly_checked_deductions']:,} new deductions and {q['newly_checked_references']:,} references. Together with
the accepted prefix, {q['total_checked_deductions']:,} deductions are now connected to the original
clause set through checked checkpoint consequences.

The remaining continuation has {q['remaining_deductions']:,} deductions and
{q['remaining_references']:,} references. Its sources are already generated and pinned;
do not regenerate them or restart accepted modules. Read
milestones/161-share18-full-replay/PILOT_COMPLETION.md and its adjacent
data/pilot-completion.json before resuming scripts/run_replay.py in bounded
batches. The driver rechecks and reuses accepted objects.

The complete contradiction, actual-snake transfer and reversal are still
pending. The universal 012034 share-18 theorem and a new global upper bound
are not established. The completed interpretation in milestone 159 and
checkpoint in milestone 160 remain accepted.

Last full paper revision: 156; next: 166. Historical updates follow.

'''
    for rel in ['README.md', 'handoff/CURRENT_STATUS.md', 'handoff/NEXT_AGENT_PROMPT.md']:
        p = R / rel
        old = p.read_bytes()
        if not old.startswith(header.encode()):
            p.write_bytes(header.encode() + old)
    completion = header.split('Last full paper revision:')[0].replace(
        '# Current result: first continuation group checked in Lean', '# Milestone 161 pilot completion')
    completion += f'''The complete transport compared all 13,224 original core clauses, reproduced
the accepted allocation and prefix, and checked ownership and packed decoding.
The 833 generated source modules contain 94,719,364 bytes. This preparation
did not repeat native unit propagation for the remaining proof.

All {q['axiom_reports']} pilot axiom reports contain only permitted standard Lean axioms.
The maximum sampled compiler private memory was {q['maximum_sampled_private_bytes']:,} bytes.
The full contradiction still requires all 2,415 continuation segments and
the final empty-clause consequence. The pilot checks the first 32 segments.

Resume from E:/Snake-in-a-box with the configured Python runtime:

```text
python -B -X utf8 milestones/161-share18-full-replay/scripts/run_replay.py --limit 24
```

The limit counts newly accepted modules; existing accepted modules are
verified and reused. One compiler may run at a time. Inspect the progress
record and batch lock before starting. Preserve failed attempts and exact
source bytes. The proof target remains the existing clause set; no new
Boolean solver query or new mathematical definition is needed.
'''
    (H / 'PILOT_COMPLETION.md').write_text(completion, encoding='utf-8')
    p = H / 'README.md'
    old = p.read_bytes()
    notice = b'# Accepted pilot update\n\nThe first32 continuation segments passed Lean. Read PILOT_COMPLETION.md and data/pilot-completion.json. The full replay remains pending. The preparation description below is historical.\n\n'
    if not old.startswith(notice):
        p.write_bytes(notice + old)
    print('RECORDED_PILOT_AND_UNCHANGED_PAPER')

if __name__ == '__main__':
    main()
