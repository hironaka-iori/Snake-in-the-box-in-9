"""Update the current paper and continuation pointers from the saved checkpoint."""
from pathlib import Path
import json,re
HERE=Path(__file__).resolve().parents[1];ROOT=HERE.parents[1]
c=json.loads((HERE/'data/checkpoint.json').read_text());assert c['paper_revision']==96
nw=len(c['checked_witness_classes']);ng=len(c['observed_geometry_classes'])
latest=(f'Latest continuation: [milestone 96](milestones/96-paper-revision/README.md) integrates the completed history-share bounds, conditional accepted-key graph coverage and joint slope/range comparison into the existing paper. It adds four statements and a complete 55-rule table, with zero new named definitions. The frozen checkpoint records {nw}/127 witness classes and {ng}/127 geometry classes. The interval remains 191 through 235, with 234 conditional.')
paper=('Current manuscript revision: [milestone 96](milestones/96-paper-revision/README.md). All 130 prior statements and the original appendix body are preserved; four statements bring the total to 134. All 13 printed snakes pass 118,673 vertex-pair checks, and all 199 labels resolve. The 55-row history table matches the checked 69-word catalogue and eight capped bounds. Authors and hyperlink settings are unchanged, and the editor and repository sources are identical. The built-in compiler could not start its helper, so no updated PDF or layout check is claimed.')
priority=('Next research priority: combine the remaining graph-weight components with the checked history credit, retaining the actual full edge key, and verify the complete potential on the defined graph, including conservative extra rows. Continue the existing witness and geometry batches. Keep the five unfinished target floors and two reference-catalogue premises explicit. Preserve case7302\'s stopped Check1 replay until a controlled isolated test. The next scheduled full paper revision is milestone 106.')
for name in ['README.md','COLLABORATION.md']:
    p=ROOT/name;s=p.read_text()
    for prefix,value in [('Latest continuation:',latest),('Current manuscript revision:',paper),('Next research priority:',priority)]:
        s,n=re.subn('^'+re.escape(prefix)+'.*$',lambda m:value,s,count=1,flags=re.M);assert n==1
    s=s.replace('The paper is revision 86 and matches the existing editor source.','The paper is revision 96 and matches the existing editor source.')
    marker='The preceding paper revision is [milestone 43]'
    if '## Historical checkpoints' not in s:s=s.replace(marker,'## Historical checkpoints\n\nThe entries below describe the evidence available at their original checkpoints.\n\n'+marker,1)
    p.write_text(s)
block=f'''## Milestone 96 checkpoint

The existing paper now integrates milestones 87–95 in dependency order:
complete history-word classification, all applicable history credits,
conditional accepted-key graph coverage, and joint optimisation of slope
and potential range on the fixed saved weighted graphs. The new appendix
lists all 55 share rules, their 69 compatible words and eight stronger caps.
No new named definition was introduced.

The revision preserves all 130 previous statements, the original appendices,
authors and hyperlink metadata. Four statements bring the total to 134.
All 13 printed paths and 118,673 vertex pairs pass the saved source checks.
The existing successful Lean receipts supporting the additions were rechecked
against their exact source, object and log bytes. No new theorem or complete
dependency rebuild is claimed for this manuscript revision.

The frozen checkpoint records {nw}/127 witness classes and {ng}/127 geometry
classes. Sessions 13482 and 23168 were confirmed running during this turn.
Inspect their current process and receipt state before any restart. Case7302
remains stopped after its Check1 timeout, with 649 successful modules.

The maintained interval is $191\\le a(9)\\le235$ edges, with 234 conditional.
The upper bound retains the inspected contributor theorem and saved audit;
a complete independent rebuild remains pending. The completed history-credit
theorem removes its local geometric premises, while the other weight components,
reference catalogues, complete coverage and global potential remain separate.

The built-in compiler failed before source compilation because its helper
could not start. No updated PDF or page-layout check is verified. The exact
diagnostic is saved in milestone 96. The next full revision is scheduled for106.

'''
p=ROOT/'handoff/CURRENT_STATUS.md';s=p.read_text();a=s.index('## Milestone 95 checkpoint');b=s.index('## Result and evidence boundary');s=s[:a]+block+s[b:]
a=s.index('The current paper is revision 86');b=s.index('## Chosen route:',a)
s=s[:a]+f'''The current paper is revision 96, by Iori Hironaka, Tommy Ma and Steven Zhan.
Its existing editor and repository sources both have SHA-256
`{c['paper_sha256']}`.
The 134 statement blocks, 199 resolved labels, 55-row history table and all
printed witnesses pass source checks. The original appendix body and all
metadata are preserved. The compiler could not start before processing the
source. The next scheduled full paper revision is milestone 106.

'''+s[b:];p.write_text(s)
p=ROOT/'handoff/README.md';s=p.read_text();a=s.index('The latest manuscript checkpoint is');b=s.index('[Milestone 94]',a)
s=s[:a]+'''The latest manuscript and continuation checkpoint is
[milestone 96](../milestones/96-paper-revision/README.md). It preserves all
130 prior statements and adds four statements, a complete history-share table,
and no new named definitions. Its [checkpoint](../milestones/96-paper-revision/data/checkpoint.json)
and [manifest](../milestones/96-paper-revision/data/file-manifest.json) preserve
the source checks, compiler failure and continuing batch observation.

[Milestone 95](../milestones/95-history-credit-integration/README.md) supplies
all concrete history-share bounds and their maximum for actual snakes.
Its exact source transformations, proof receipts and literal-credit audit remain
the evidence for that completed mathematical component. The remaining global
weight and potential assembly is unfinished.

'''+s[b:]
s=s.replace('The latest paper is revision 86','The latest paper is revision 96').replace('compiler attempt at milestone 86','compiler attempt at milestone 96')
s=s.replace('is the closed reference proofs and concrete finite coverage/endpoint certificates;\ncredit interpretation follows.','is the closed reference proofs and complete concrete finite coverage. The history\ncredit is complete; other weight components and full-key preservation remain.')
p.write_text(s)
p=ROOT/'handoff/NEXT_AGENT_PROMPT.md';s=p.read_text().replace('Paper revision 86 is current.','Paper revision 96 is current; read its checkpoint and verification report.')
a=s.index('The paper revision is now due at milestone 96.');b=s.index('After revision, assemble',a)
s=s[:a]+'''The paper was revised at milestone 96. Its four additions state the exact
compatible-word classification, completed history bound, conditional graph
coverage and fixed-model joint optimisation. It adds no named definitions.
Use ordinary notation and define a concept only when essential and repeatedly
used. The next scheduled full revision is milestone 106.

'''+s[b:];s=s.replace('After revision, assemble','Now assemble',1)
s=s.replace('The frozen milestone 95 checkpoint has 86/127 witness classes, 89/127 geometry',f'The frozen milestone 96 checkpoint has {nw}/127 witness classes, {ng}/127 geometry')
s=s.replace('Paper revision 86 has130 statements. The next full rewrite is scheduled for 96.','Paper revision 96 has 134 statements and no new named definitions.\nThe next full rewrite is scheduled for milestone 106.')
p.write_text(s)
p=ROOT/'milestones/README.md';s=p.read_text();marker='- [Milestone 95:';a=s.index(marker)
assert '- [Milestone 96:' not in s
s=s[:a]+'- [Milestone 96: paper revision](96-paper-revision/README.md). Four statements, complete 55-rule history catalogue, all prior statements and metadata preserved, zero new named definitions. Source checks pass; preview unavailable before compilation.\n\n'+s[a:];p.write_text(s)
p=ROOT/'RESEARCH_LEDGER.md';s=p.read_text();assert '## Milestone 96:' not in s
s+='\n\n## Milestone 96: paper revision\n\n3 November 2026, Japan time. '+latest+'\n\n'+paper+'\n\n'+priority+'\n';p.write_text(s)
p=ROOT/'paper/README.md';s=p.read_text();a=s.index('All maintained TeX sources belong here.');b=s.index('The main source is standalone',a)
s=s[:a]+'''The repository copy of the main paper belongs here. The currently open editor
source is `D:/Codex/2026-10-13/new-chat/outputs/snake9_research.tex`.
Revise that existing source in place and synchronize this repository copy.
Preserve the local hyperlink configuration and author metadata.

'''+s[b:]
a=s.index('Current logical revision:');s=s[:a]+'''Current logical revision: milestone 96. The maintained interval is
$191\\le a(9)\\le235$ edges; the target 234 remains conditional. The paper has
134 statement blocks and 199 resolved labels. The complete history-share
table lists 55 rules and 69 compatible words, with eight stronger capped bounds.
All 130 previous statements and the original appendix body are preserved.
All 13 printed snakes pass 118,673 pairwise adjacency checks. No new named
definition was added. The exact editor and repository sources agree.

The current built-in preview attempt failed before source compilation because
the compiler helper could not start. An updated PDF and page layout have not
been verified. Existing PDFs must not be treated as outputs of this revision.
See [revision 96](../milestones/96-paper-revision/README.md) for the saved checks.
''';p.write_text(s)
(HERE/'README.md').write_text(f'''# Milestone 96: paper revision

The existing paper now includes the completed 55-rule history-share argument,
conditional coverage of the graph defined by accepted full keys, and the
joint slope/range obstruction for three fixed weighted graphs. A complete
appendix lists 69 compatible words and eight stronger capped bounds.

All 130 previous statements, the original appendix body, authors and hyperlink
settings are preserved. Four statements bring the total to 134. There are
zero new named definitions. The source verifier checks all 199 labels, the
exact 55-row table, all 13 printed snakes and 118,673 vertex pairs. It also
rechecks the existing proof receipts and exact arithmetic; it adds no new
Lean theorem and does not rebuild the inherited dependency closure.

Both source copies have SHA-256 `{c['paper_sha256']}`.
The built-in compiler could not start its helper before source compilation.
No updated PDF or page-layout check is verified.

Read [verification](data/verification.json), [compiler diagnostic](data/compiler-result.json),
[checkpoint](data/checkpoint.json), [source audit](audit/paper-source-audit.md),
and [continuation directions](next-steps.md). The previous source is preserved
in `data/paper-before.zip`. The manifest pins the completed evidence.

The frozen batch snapshot records {nw}/127 witness classes and {ng}/127 geometry
classes. Both inherited runners were active during this turn. Case7302 remains
stopped after its preserved Check1 timeout. The interval remains
$191\\le a(9)\\le235$ edges, with 234 conditional and a complete independent
rebuild of the contributor upper-bound proof pending.
''')
p=HERE/'README.md';s=p.read_text();p.write_text(s)
print('UPDATED_MILESTONE96_DOCUMENTS',nw,ng)
