"""Save the current result and a bounded continuation using exact status records."""
from pathlib import Path
import json
H=Path(__file__).resolve().parents[1];R=H.parents[1]
read=lambda p:json.loads(p.read_text(encoding='utf-8-sig'))
assert read(H/'data/TwoCycles145-audit.json')['status']=='PASS'
assert read(H/'data/direct-replay.json')['status']=='PASS_COMPLETE_DIRECT_RUP_REPLAY'
assert read(H/'data/chunked-bridge-completion.json')['status']=='PARTIAL_ALL104_PART_TRUTH_CHECKED_FINAL_ASSEMBLY_TIMEOUT'
summary='''# Research update: milestone 145

Two saved cycles force comparison at least235+95/2348 even after both
012301 and012340 share floors are raised to16, with arbitrary existing
uniform occurrence credit and012034 floor. Other weights and the graph
remain fixed. Lean checks this obstruction and325F+159G>9074 as a necessary
joint-floor condition. The012032 share16 target must also be addressed for
the proposed three-floor combination; it adds57 to the eleven-cycle.

The saved012301 certificate passed complete independent replay:285541
deductions,31017505 references,12977 original core inputs. Actual-snake
Lean interpretation remains pending. All104 initial-tree parts passed their
truth-transfer checks, but the full assembly timed out. No local share16
or share18 theorem, and no new global bound, is claimed.

Read [the complete checkpoint](milestones/145-countfree-012301/MATHEMATICAL_NOTE.md).
Goal ACTIVE. Next split the initial-database proof into smaller checked
pieces, then reuse the verified012301 certificate. Paper145 preserves
authors and preamble; full rewrite remains due146. Compilation status is
recorded separately from source checks.
'''
(H/'README.md').write_text(summary.replace('(milestones/145-countfree-012301/MATHEMATICAL_NOTE.md)','(MATHEMATICAL_NOTE.md)'),encoding='utf-8')
for name in ['README.md','COLLABORATION.md','RESEARCH_LEDGER.md','WORKSPACE.md','milestones/README.md','handoff/README.md','handoff/CURRENT_STATUS.md']:
    p=R/name;old=p.read_text(encoding='utf-8');assert not old.startswith('# Research update: milestone 145')
    local=summary.replace('(milestones/145','(../milestones/145') if '/' in name else summary
    p.write_text(local+'\n## Earlier record\n\n'+old,encoding='utf-8')
prompt='''# Continue after milestone145

Work in E:/Snake-in-a-box. Use the tensai-bishoujo skill with the user's
formal voice, no emojis or unnecessary definitions. Keep the open editor
D:/Codex/2026-10-13/new-chat/outputs/snake9_research.tex and paper mirror
synchronised. Preserve authors Iori Hironaka, Tommy Ma, Steven Zhan,
preamble and hypersetup. Leave unrelated .gitignore and milestone50
critical-family changes intact. Goal ACTIVE, this round made progress.

Read145/MATHEMATICAL_NOTE.md and data/checkpoint.json under milestones/.
Main mathematical result: with other weights/edges fixed,012301/012340
floors16 plus arbitrary existing occurrence credit and012034 floor cannot
bring comparison below235. Exact lower bound551875/2348=235+95/2348.
Fourteen-cycle:7mu<=3424+2F+G,2mu<=496+F+R. Eleven-cycle:11mu<=5399+4C.
With B24 a successful comparison needs325F+159G>9074. Thus F16 would need
G>=25 while the eleven-cycle is unchanged. Better use existing012032
share16, which adds57 to that cycle. Both cycles then have mean496 atC0
with all three proposed floors16. This is a saved-cycle argument only.
14 arithmetic statements passed Lean; inspect receipts and bounded review.

Current target remains count-free012301 share16, both orientations. Its
original72/critical-current pysat3-cap15 certificate has11378 variables,
92656 clauses,16 induced-eight-cycle cuts (6 in core),12977 core clauses.
145 conversion-long completed, and direct-replay.json verifies285541
deductions/31017505 references to the final contradiction. Full input/core
and exact archives were independently audited. No actual share theorem yet.
Do not rerun the timed-out90s compact-core attempt or first conversion.
Exact originals are local; scripts/restore_proofs.py restores published gzip
archives after checking hashes. Historical conversion and failed traces
are intentionally preserved. Full proof uses original input identities.

Initial-tree work is on preserved144 data: InputTree145 generic soundness
passed;28 chunked modules/419 reports passed, including104 part truth
transfers. ChunkTruthAssemblyFixed145 timed out181.610s under180s limit;
peak sampled private memory1.25GB. No accepted final theorem/object.
PrefixTruth145 is prepared but uncompiled. Do not infer whole-tree truth
from part checks. Next split original-CNF-to-chunk truth extraction from
final constructor assembly into separately checked modules, preserving
all prior failures. Then generate/replay012301 using exact key and variable
transport, original core IDs, justified cycle cuts and final geometry.

Do not spend graph runs retuning uniform credit on only the two floors:
the two-cycle obstruction already rules it out. Further conditional graph
tests must specify the three-floor profile and inherited assumptions.
The maintained191--235 interval and conditional234 have unchanged global
proof limits.196 and optimum remain unresolved.

Paper145 is targeted; last full136,next146. Always compile the saved editor
file with the built-in tool after edits. Tool preparation may fail before
TeX; record exact diagnostics and do not claim a PDF. Fetch each round,
stage only manifest files, quiet commit/push and verify remote. Preserve
audited bytes. Lean requires>=1.5GiBfree, at most2 existing Lean processes;
new runner caps its own process3GiB and free-memory floor768MiB. Fullgraph
requires>=3GiBfree and no other graph run. Inspect115's actual process and
latest record before acting; never duplicate its completion driver. The
point-in-time145 batch observations are not a substitute for current state.
'''
(R/'handoff/NEXT_AGENT_PROMPT.md').write_text(prompt,encoding='utf-8')
print('Saved145 research checkpoint and continuation prompt.')
