from pathlib import Path
import hashlib,json
H=Path(__file__).resolve().parents[1];R=H.parents[1]
summary='''# Research update: milestone 127

The direct-clause representation of the existing lower count bounds is checked.
One Lean module proves five generic counting statements. An independent replay
derives all 235 concrete clauses from the original 106348 inputs using 132921
ordered references. No new definition or six-count floor is introduced.

Replacing six lower counters removes 4917 clauses and makes 2457 auxiliary
variables unused. The reduced input has 101666 clauses and 4820 occurring
variables, with exact input mapping for later proof transport. Both changed
encodings timed out after 180 seconds; neither returned a model or contradiction.
The first 1000 native deductions of each trace passed bounded original-input
replay. This does not verify a complete contradiction. Partial traces are
preserved locally and in lossless gzip archives.

The maintained range remains 191–235 with the documented independent-rebuild
limitation. The optimum, 196, and the needed conditions for 234/233 remain open.
Paper revision 126 is unchanged; the next full revision is 136.

The next focused task is to expose the proved second/fourth pair sum at least
eight in the 0120324 encoding. It uses 42 corner occurrences over 37 vertices;
the equivalent selected-occurrence cap is 34. The new counter and its semantic
connection are not implemented. See
`milestones/127-direct-cardinality/data/next-pair-task.json`.
'''
before={}
for name in ['README.md','COLLABORATION.md','milestones/README.md','handoff/README.md','handoff/CURRENT_STATUS.md']:
 p=R/name;before[name]=hashlib.sha256(p.read_bytes()).hexdigest();t=p.read_text(encoding='utf-8')
 assert not t.startswith('# Research update: milestone 127')
 p.write_text(summary+'\n## Earlier record\n\n'+t,encoding='utf-8',newline='\n')
p=R/'RESEARCH_LEDGER.md';before[p.name]=hashlib.sha256(p.read_bytes()).hexdigest()
p.write_text(p.read_text(encoding='utf-8')+'\n\n'+summary.replace('# Research update: milestone 127','## Milestone 127: direct-clause equivalence and unresolved encoding tests')+'\n',encoding='utf-8',newline='\n')
p=R/'handoff/NEXT_AGENT_PROMPT.md';before[p.relative_to(R).as_posix()]=hashlib.sha256(p.read_bytes()).hexdigest()
t='''# Continuation after milestone 127

Work in E:/Snake-in-a-box. Use the requested research skill. Keep prose precise;
introduce a definition only when essential and used repeatedly. Fetch GitHub
and inspect the current checkout before making changes. Preserve unrelated
.gitignore and milestone 50 critical-family edits and active proof jobs.

Read `milestones/127-direct-cardinality/MATHEMATICAL_NOTE.md`, its independent
prelude review, reduced-encoding review, Lean derivation receipt, and checkpoint.
The 235 direct clauses are all derived from the original 106348 inputs in
Python. Five generic cardinality statements passed Lean. Concrete prelude RUP
checking and complete snake-refutation checking are separate requirements.

Both native encodings timed out after 180 seconds. The reduced formula has
101666 clauses and 4820 occurring variables. Preserve original variable IDs and
its input map. Native derived IDs map by x+4917, then prepend the 235 derivations.
Trimming must use the original 106348 inputs. Do not treat the added clauses as
trusted axioms. Only the first 1000 native deductions per trace were replayed.
The partial traces have verified gzip archives; restore and check original
hashes before running auditors that require raw traces on a fresh checkout.

Next selected task: implement data/next-pair-task.json in milestone 127.
The already-proved 012032 prefix inequality is alpha_(r+2)+alpha_(r+4)>=8.
Its 42 corner occurrences represent 37 distinct vertices; preserve duplicates.
Expose it as at most 34 selected occurrences, with a checked canonical prefix,
missing-corner and counter-semantic interpretation. This is an additional
known geometric theorem, not yet an RUP-derived consequence of the saved CNF.
Do not claim original-only proof preservation for the new pair counter without
providing its derivation, or instead its complete Lean semantic interpretation.
The pair input is not encoded or searched. Avoid repeating the two unchanged
wall-time-limited inputs merely to obtain another timeout.

The working local hypothesis is a six-count floor 23 for 0120324. It remains
unproved. It would remove the sum-22 edge of the saved conditional cycle, but
does not automatically improve the full graph minimum or a global length bound.
The universal floor 25, or a sufficient total shortfall bound retaining 2s0,
remains a separate route to 234. The precise hypotheses are in paper revision 126.
The current range remains 191–235 with the contributor-proof rebuild limitation.
The optimum and 196 remain unresolved. Do not mark the overall goal complete.

The 104/115/122 drivers were all observed live in milestone 127; its point-in-time
snapshot reported 338 selected potential modules, 507 total-count modules, and 311
endpoint-plan receipts. These partial counts prove no completed batch. Inspect
their actual processes and records before continuing or restarting anything.

The paper remains revision 126, SHA256
4667daec19f0b83af9fb129a263c8ae992757105414bad817c1ad13e1e11bb90,
identical at E:/Snake-in-a-box/paper/snake9_research.tex and the open editor
D:/Codex/2026-10-13/new-chat/outputs/snake9_research.tex. Preserve all authors
and hyperlink settings. Its last built-in compile failed before TeX in the
Windows helper. The next scheduled full paper revision is 136. Do not rewrite
the paper on every round or put Lean implementation names in its mathematical
text. Continue mathematical work and save/push reviewed checkpoints.
'''
p.write_text(t,encoding='utf-8',newline='\n')
p=R/'WORKSPACE.md';before[p.name]=hashlib.sha256(p.read_bytes()).hexdigest();t=p.read_text(encoding='utf-8');a=t.index('## Current direction');b=t.index('## Historical checkpoint notes',a)
t=t[:a]+'''## Current direction

Current checkpoint: [milestone 127](milestones/127-direct-cardinality/README.md).
The selected route uses six consecutive singleton counts and empty squares.
The checked direct-clause encoding did not resolve 0120324 in two bounded runs.
Next implement the proved pair-count inequality using the pinned specification
in `milestones/127-direct-cardinality/data/next-pair-task.json` and check its
new counter semantics. The maintained range remains 191–235; no new count floor
or unconditional bound is claimed. Paper revision 126 is unchanged, with its
compiler limitation preserved; next full revision 136. Inspect live proof
drivers before restarting any work.

'''+t[b:]
p.write_text(t,encoding='utf-8',newline='\n')
(H/'data/document-update.json').write_text(json.dumps(dict(before_sha256=before,updated=list(before)),indent=2)+'\n',encoding='utf-8')
print('Updated eight continuation documents.')
