from pathlib import Path
import hashlib,json
H=Path(__file__).resolve().parents[1];R=H.parents[1]
summary='''# Research update: milestone 126

The manuscript is revised through milestone 125. The direct six-count and
empty-square argument now precedes the long graph construction. No new
definition is added, and temporary joint-budget aliases are removed.
The authors and complete local hyperlink settings are preserved.

The paper distinguishes the proved 0123041 six-count bound, sharp 012032
pair theorem and necessary 0120324 intervals from the unresolved universal
floors and shortfall assumptions needed for 234 or 233. Twenty reference
entries are discharged; 1358 and the five additional share targets remain.
The maintained range is 191–235, with its documented independent-rebuild
limitation. Neither the optimum nor 196 is established.

All 16 printed snakes pass 148857 pair checks. Exact evidence from 188 prior
Lean modules and 139 dependency reports is rechecked; there is no new Lean
compilation this round. The built-in PDF compiler failed in its Windows helper
before processing TeX. The source checks pass; PDF compilation and layout
remain unverified. The next scheduled full paper revision is 136.

See milestone 126's README, manuscript verification and reviews. The next
research task remains the unimplemented 0120324 encoding proposal saved in
milestone 125. Inspect the live 104/115/122 drivers before resuming any job.
'''
before={}
for name in ['README.md','COLLABORATION.md','milestones/README.md','handoff/README.md','handoff/CURRENT_STATUS.md']:
 p=R/name;before[name]=hashlib.sha256(p.read_bytes()).hexdigest()
 text=p.read_text(encoding='utf-8');assert not text.startswith('# Research update: milestone 126')
 p.write_text(summary+'\n## Earlier record\n\n'+text,encoding='utf-8',newline='\n')
p=R/'RESEARCH_LEDGER.md';before[p.name]=hashlib.sha256(p.read_bytes()).hexdigest()
p.write_text(p.read_text(encoding='utf-8')+'\n\n'+summary.replace('# Research update: milestone 126','## Milestone 126: full paper revision and notation reduction')+'\n',encoding='utf-8',newline='\n')
p=R/'handoff/NEXT_AGENT_PROMPT.md';before[p.relative_to(R).as_posix()]=hashlib.sha256(p.read_bytes()).hexdigest()
t=p.read_text(encoding='utf-8')
a=t.index('Milestone 126 is the scheduled full paper revision.');b=t.index('\nCurrent results:',a)
t=t[:a]+'''Milestone 126 completed the scheduled paper revision through result 125.
Read its README, four audit reports and data/verification.json. The open editor
source and E:/Snake-in-a-box/paper mirror are identical, with all authors and
hyperlink settings preserved. Seven statements were added; no definitions
were added. All prior mathematical content and appendices are retained,
with three notation/title clarifications. The built-in compiler failed before
TeX because of its Windows helper, so PDF compilation/layout are unverified.
The next scheduled full paper revision is 136. Do not repeat the full review.
'''+t[b:]
t=t.replace('# Continuation after milestone 125','# Continuation after milestone 126')
t=t.replace('Verify the current checkpoint and fetch the remote before making changes.','Verify the milestone-126 checkpoint and fetch the remote before making changes.')
p.write_text(t,encoding='utf-8',newline='\n')
p=R/'WORKSPACE.md';before[p.name]=hashlib.sha256(p.read_bytes()).hexdigest()
t=p.read_text(encoding='utf-8');a=t.index('## Current direction');b=t.index('\n\n\nThe latest theorem',a)
t=t[:a]+'''## Current direction

Current checkpoint: [milestone 126](milestones/126-paper-revision/README.md).
The selected route uses six consecutive singleton counts and retains empty
squares. The maintained range is 191–235 with the documented upper-proof
rebuild limitation; universal local floors and sufficient shortfall bounds
remain unresolved. The manuscript revision through 125 is saved in both
source locations, with no new definitions and preserved authors/settings.
The built-in PDF compiler failed before TeX; source verification passed.
The next full paper revision is 136.

Next task: implement the reviewed cardinality-clause proposal saved in
milestone125/data/next-encoding-task.json, using its actual repository path
`milestones/125-critical-six-count/data/next-encoding-task.json`.
Inspect existing live proof drivers before restarting anything.

## Historical checkpoint notes
'''+t[b:]
p.write_text(t,encoding='utf-8',newline='\n')
(H/'data/document-update.json').write_text(json.dumps(dict(before_sha256=before,updated=list(before)),indent=2)+'\n',encoding='utf-8')
print('Updated eight research and continuation documents.')
