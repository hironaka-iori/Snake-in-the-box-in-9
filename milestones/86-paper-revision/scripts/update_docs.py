"""Synchronize current project summaries with the checked manuscript revision."""
from pathlib import Path
import json
HERE=Path(__file__).resolve().parents[1];ROOT=HERE.parents[1]
r=json.loads((HERE/'data/verification.json').read_text());assert r['status']=='PASS_PAPER86_SOURCE_AND_MATHEMATICS'
digest=r['paper_sha256']
latest='Latest continuation: [milestone 86](milestones/86-paper-revision/README.md) revises the existing paper to include milestones 77–85. It adds five propositions, incorporates the completed 012310 share theorem and the exact graph interfaces, and explains the unsaturated-cycle obstruction. Seven new Lean logic checks pass; all 13 printed paths and 118,673 vertex pairs pass. The built-in compiler failed before source compilation, so no new PDF is verified. Case7302 remains active and pending. The interval remains 191 through 235, with 234 conditional; see [the current handover](handoff/README.md).'
paper='Current manuscript revision: [milestone 86](milestones/86-paper-revision/README.md). The paper has 128 statement blocks and 187 resolved labels. It distinguishes the completed mean483 comparison, the single-target rational comparison and the full conditional234 target. Four interface propositions and the cycle obstruction have explicit proofs and evidence limits. Authors, hyperlink settings, all previous appendix material and all printed witnesses are preserved. The editor and repository sources match. The app compiler could not start; no updated PDF or layout check is claimed.'
for name in ['README.md','COLLABORATION.md']:
    path=ROOT/name;s=path.read_text()
    for start,replacement in [('Latest continuation:',latest),('Current manuscript revision:',paper)]:
        a=s.index(start);b=s.index('\n\n',a);s=s[:a]+replacement+s[b:]
    s=s.replace('The scheduled full paper revision is milestone 86.','The revised paper is milestone 86; the next full revision is scheduled for 96.')
    s=s.replace('The paper remains revision 76 and matches the existing editor source.','The paper is revision 86 and matches the existing editor source.')
    path.write_text(s,encoding='utf-8')
path=ROOT/'handoff/CURRENT_STATUS.md';s=path.read_text()
a=s.index('The current paper is revision');b=s.index('## Chosen route:',a)
s=s[:a]+f'''The current paper is revision 86, with authors Iori Hironaka, Tommy Ma and
Steven Zhan. Its repository and existing editor copies have SHA256
`{digest}`.
It incorporates milestones 77–85 and has 128 statement blocks: 122 retained
unchanged, one strengthened local-share theorem and five new propositions.
All 13 printed paths, 118,673 vertex pairs and 187 labels pass source checks.
Seven new Lean checks cover the abstract bonus argument and conditional
comparison arithmetic. The original appendix body and all metadata are preserved.
The built-in compiler failed before reading the source; no new PDF or layout
check is claimed. The next full revision is scheduled for milestone 96.

'''+s[b:]
s=s.replace('Its manifest identifies the current shared handover versions.',
            'Milestone 86 incorporates these results into the paper; its manifest identifies the current shared handover versions.')
path.write_text(s,encoding='utf-8')
path=ROOT/'handoff/NEXT_AGENT_PROMPT.md';s=path.read_text()
s=s.replace("`handoff/CURRENT_STATUS.md`, and milestone 85's README and exact checkpoint. Milestone 83 preserves the active case 7302 proof sources.",
            "`handoff/CURRENT_STATUS.md`, milestone 86's paper checkpoint and milestone 85's proof README. Milestone 83 preserves the active case 7302 proof sources.")
a=s.index('hyperlink settings. Revision');b=s.index('The existing editor file is',a)
s=s[:a]+'''hyperlink settings. Revision 86 is the latest paper and incorporates milestones
77 through 85. It has 128 statements and seven new logic audits; source checks
pass, while the editor compiler failed before source compilation. The next
full revision is scheduled for 96. '''+s[b:]
path.write_text(s,encoding='utf-8')
path=ROOT/'handoff/README.md';s=path.read_text()
marker='The current proof checkpoint is'
insert='''The latest manuscript and handover checkpoint is
[milestone 86](../milestones/86-paper-revision/README.md), with 128 statements,
seven new Lean checks and all printed witnesses preserved and rechecked.
The editor compiler failed before source compilation; no new PDF is verified.
Use its [checkpoint](../milestones/86-paper-revision/data/checkpoint.json) and
[manifest](../milestones/86-paper-revision/data/file-manifest.json) for the
current paper, shared handover versions and replay observation.

'''
s=s.replace(marker,insert+marker,1)
s=s.replace('for current evidence, handover versions and a later observation of the active replay.',
            'for that proof round and its historical handover and replay observation.')
s=s.replace("use milestone 85's manifest for their current versions.","use milestone 86's manifest for their current versions.")
s=s.replace('The latest paper is revision 76, unchanged and hash-matched during milestone 85.',
            'The latest paper is revision 86, updated in place with a hash-matched repository mirror.')
s=s.replace('The compiler retry at milestone 77 failed\nbefore source compilation; its diagnostic is saved there.',
            'The compiler attempt at milestone 86 failed\nbefore source compilation; its diagnostic is saved there.')
path.write_text(s,encoding='utf-8')
path=ROOT/'milestones/README.md';s=path.read_text()
s=s.replace('The manuscript is at revision 76.','The manuscript is at revision 86.')
marker='- [Milestone 85:'
s=s.replace(marker,'- [Milestone 86: revised paper and precise proof scope](86-paper-revision/README.md). 128 statements, seven new Lean checks, all 13 printed paths rechecked; five target shares and global assembly remain pending. Editor compilation failed before source processing.\n\n'+marker,1)
path.write_text(s,encoding='utf-8')
path=ROOT/'RESEARCH_LEDGER.md';s=path.read_text()
assert '## Milestone 86:' not in s
s+='''

## Milestone 86: paper revision and proof scope

2 November 2026. The existing editor document and repository mirror now incorporate milestones77–85. The paper has 128 statement blocks:122 previous statements unchanged, the count-independent share theorem strengthened by012310>=12, and five new propositions for the actual state sequence, filters, history exclusions, conditional reference union and unsaturated-cycle obstruction. All original appendix content,13 printed snakes and118,673 vertex pairs are preserved and checked. All187 labels resolve; authors and hyperlink metadata are unchanged. Seven fresh Lean checks cover the abstract cycle-family argument and conditional comparison arithmetic.

The completed-local model is now clearly identified as mean483, range551; mean480 is historical. The pending012034 floor gives9259/19 with scaled range11301 and still integer235. The full496/600 comparison remains conditional234 with five local shares, closed reference imports, retained-array membership, credit interpretation and complete potential replay pending. The built-in compiler again failed before reading the TeX source because of its Windows execution environment; no updated PDF is verified. The complete original was independently read, all additions reviewed, and history-notation and converse-status issues corrected. Case7302 continues under its existing driver. The next scheduled paper revision is96; the next proof task is exact retained-array membership under the current explicit premises.
'''
path.write_text(s,encoding='utf-8')
print('Updated seven current project documents for paper revision86')
