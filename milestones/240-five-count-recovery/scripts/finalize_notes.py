from pathlib import Path
import json
H=Path(__file__).resolve().parents[1]; R=H.parents[1]
assert json.loads((H/'data/matrices-replay.json').read_bytes())['status']=='PASS'
assert json.loads((H/'data/independent-geometry.json').read_bytes())['status']=='PASS_GEOMETRIC_CLASS_COVERAGE'
assert json.loads((H/'data/EightCubeObstruction240-audit.json').read_bytes())['status']=='PASS'

def edit(name, replacements):
 p=H/name; text=p.read_text(encoding='utf-8')
 for old,new in replacements:
  assert text.count(old)==1,(name,old[:100])
  text=text.replace(old,new)
 p.write_text(text,encoding='utf-8',newline='\n')

edit('MATHEMATICAL_NOTE.md',[("**Publication gate:** the full run of 372 Lean matrix modules is pending in this draft. Their acceptance must be established from the root worker's complete receipt before describing all 372 as Lean-checked. Even after acceptance, these are literal matrix theorems.","**Accepted arithmetic:** all 372 Lean matrix modules passed, as recorded in data/matrices-replay.json and the individual source-bound receipts. An independent enumeration of 2,699,004 actual vertex triples recovered the same 372 distance matrices. These are literal matrix theorems.")])
edit('STRUCTURAL_NOTE.md',[("The finite Lean source named below was prepared without running a compiler; acceptance must be read from the parent's eventual receipt.","The explicit finite Lean source named below subsequently passed the guarded compiler, with eight accepted axiom reports in data/EightCubeObstruction240-audit.json. Its scope remains narrower than the written structural classifications.")])
edit('HANDOFF.md',[
("This handoff was prepared while the complete 372-module Lean receipt was pending. It does not itself certify completion or change the goal status. The root worker owns the final publication and pause.","All 372 matrix implications and the explicit eight-point witness passed Lean. The separate direct enumeration covered 2,699,004 vertex triples and recovered the same 372 classes. Source-bound receipts are retained. Publish the checkpoint, then use the goal tool to record the requested pause."),
("The 372 literal matrix implications may be called Lean-checked only after the root worker obtains their complete accepted receipt.","All 372 literal matrix implications passed Lean checking."),
("Its acceptance must be read from the root receipt.","It passed Lean with eight axiom reports; its receipt is data/EightCubeObstruction240-audit.json."),
("paper-addition.tex and short-addition.tex: exposition with an explicit pending-kernel gate.","paper-addition.tex and short-addition.tex: accepted arithmetic and written cube argument with explicit verification scope."),
("scripts/independent_geometry.py: separate direct-vertex coverage method; its execution status belongs to the root worker's receipt.","data/independent-geometry.json: separate direct enumeration of all 2,699,004 actual vertex triples, matching all 372 classes."),
("Before publication, replace pending claims only when the corresponding accepted receipts exist.","All acceptance claims above are backed by the corresponding completed receipts.")])
edit('NEXT_STEP.md',[("372 five-position implications subject to the final Round 240 accepted receipt.","372 accepted five-position implications, recorded in the final Round 240 receipt.")])

contributor=json.loads((H/'data/contributor-status.json').read_bytes())
current=(H/'HANDOFF.md').read_text(encoding='utf-8')
current += '\n## Publication and review record\n\nThe complete written source was reviewed at Round 240: all 13,254 pre-edit main lines and all 1,084 pre-edit explanation lines, followed by review of the integrated changes. The next full review is due at Round 250. This does not independently rebuild the archived upper-bound dependency chain. All three authors and local hypersetup settings are retained. The original editor files and paper mirrors match. Compilation outcomes are recorded separately in data/.\n\nThe contributor branch was refreshed at revision '+contributor['branch_revision']+'. Its new trackB report explicitly claims no new bound or Lean build. It investigates local-floor limitations toward conditional 220; these numerical observations were read without independent replay. The completed 231 source is unchanged.\n\nUse one heavy worker/compiler, at least 1 GiB free memory at startup, 768 MiB reserve, 256 MiB private-memory ceiling, and one Lean thread with 60 seconds per module. Preserve unrelated edits to .gitignore and milestone 50. No Round 241 search is running.\n'
(H/'HANDOFF.md').write_text(current,encoding='utf-8',newline='\n')
(R/'handoff/CURRENT_STATUS.md').write_text('Artifact paths below are relative to milestones/240-five-count-recovery unless stated otherwise.\n\n'+current.replace('Read STRUCTURAL_NOTE.md','Read ../milestones/240-five-count-recovery/STRUCTURAL_NOTE.md').replace('follow NEXT_STEP.md','follow ../milestones/240-five-count-recovery/NEXT_STEP.md'),encoding='utf-8',newline='\n')
prompt='''# Resume only on explicit instruction

Research pauses after Round 240. Do not begin Round 241 until the user resumes it.

Read CURRENT_STATUS.md, ../milestones/240-five-count-recovery/MATHEMATICAL_NOTE.md, STRUCTURAL_NOTE.md, NEXT_STEP.md, and data/completion.json in that milestone. All 372 five-point matrix implications passed Lean, while the full cube assembly still covers three missing counts. Five-count recovery is a written theorem with native geometric coverage and accepted literal arithmetic. The minimum nonzero neighbour-count support is six through nine. No new longer snake or global length bound was obtained; the maintained interval is 191--231 with the contributor's full independent rebuild pending.

The preferred continuation uses the actual bound on count differences, at most 9, and generator-coordinate structure. The explicit eight-point matrix has nonzero unrestricted integer solutions of magnitude 21, so do not extrapolate an unbounded zero-solution lemma. The symmetric eight-point configuration and entire-support stars are excluded by written arguments, but disconnected components have nonzero even couplings. Six-count recovery remains open. See NEXT_STEP.md for possible outcomes and precise scope. Alternatively complete the missing four/five-count Lean cube bridge. Preserve the frozen construction searches and unrelated local edits.

Keep research in E:/Snake-in-a-box. Edit the existing D:/Codex/2026-10-13/new-chat/outputs/snake9_research.tex and snake9_frontier_explanation.tex in place, retaining the editor and exact paper mirrors. Preserve all three authors and local hypersetup. The full written manuscript review was completed at 240; next due 250. Respect the single-heavy-worker and recorded memory/compiler limits. Mathematical deductions, native finite computations, literal Lean implications and cube-level assembly must remain distinguishable.
'''
(R/'handoff/NEXT_AGENT_PROMPT.md').write_text(prompt,encoding='utf-8',newline='\n')
readme=R/'README.md'
old=readme.read_text(encoding='utf-8')
assert old.startswith('# Current result after round 239')
head='''# Current result after round 240

Any 507 of 512 labelled neighbour counts determine a binary selection in Q9. The written five-count recovery proof is supported by two independent geometry enumerations and 372 accepted Lean matrix implications. The fully assembled Lean cube theorem covers three missing counts. The minimum number of changed counts between different selections is now between six and nine. The conditional eight-count result remains valid when no missing pair is at distance eight.

An explicit symmetric eight-point matrix admits nonzero integer solutions of amplitude 21. This disproves a blanket extension of the unbounded integer method, while the actual count bound 9 excludes these solutions. A written character argument classifies all solutions for that matrix, and a separate written proof excludes entire-support distance-eight stars of at most eight positions. General six-through-eight recovery is open.

No longer snake or new global snake-length bound was obtained. The maintained interval is 191--231; independent rebuilding of the contributor's completed 231 theorem remains pending. Round 240 includes the complete written-manuscript review. Publish and pause after 240; no Round 241 work before explicit resumption.

Read [the proof](milestones/240-five-count-recovery/MATHEMATICAL_NOTE.md), [structural findings](milestones/240-five-count-recovery/STRUCTURAL_NOTE.md), [evidence](milestones/240-five-count-recovery/data/completion.json), [handoff](handoff/CURRENT_STATUS.md), and [next step](milestones/240-five-count-recovery/NEXT_STEP.md).

## Earlier checkpoints

'''
readme.write_text(head+old,encoding='utf-8',newline='\n')
(H/'README_CHECKPOINT.md').write_text(head.split('## Earlier checkpoints')[0],encoding='utf-8',newline='\n')
print('Notes and current handoffs finalized; publication and goal pause remain subsequent steps.')
