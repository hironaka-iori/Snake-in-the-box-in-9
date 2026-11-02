"""Refresh current pointers and preserve historical milestone records."""
from pathlib import Path
ROOT=Path(__file__).resolve().parents[3]
current=('Current manuscript revision: [milestone 76](milestones/76-paper-revision/README.md). '
 'The revised argument includes boundary contribution 21, completed and pending shares, exact history recognition, '
 'conditional 234 and the short-walk obstruction. All 116 old statements and 13 snakes are preserved; seven additions '
 'give 123 statements. All 180 labels and 118,673 vertex-pair checks pass, as do six new Lean arithmetic checks. '
 'The editor and repository sources match, with authors and hyperlink settings preserved. '
 'The app compiler failed before source compilation; no updated PDF is verified.')
latest=('Latest continuation: [milestone 76](milestones/76-paper-revision/README.md) completes the scheduled paper revision '
 'and six conditional arithmetic checks. The bound 234 retains six local share premises and the incomplete global graph proof. '
 'Case 7305 replay was active at the saved checkpoint; inspect its live process before restarting. '
 'Use [handoff/README.md](handoff/README.md) for current instructions.')
for name in ['README.md','COLLABORATION.md']:
    path=ROOT/name;paras=path.read_text(encoding='utf-8').split('\n\n')
    for i,p in enumerate(paras):
        if p.startswith('Current manuscript revision:'):paras[i]=current
        elif p.startswith(('Latest research:','Latest continuation:')):paras[i]=latest
    s='\n\n'.join(paras).replace('The paper remains revision66 and matches the existing editor source.',
      'The paper is now revision 76 and matches the existing editor source.')
    s=s.replace('The manuscript remains at revision 66, with its next full rewrite scheduled for milestone 76.',
      'Revision 76 now incorporates these results; the complete graph proof remains pending.')
    path.write_text(s,encoding='utf-8')
path=ROOT/'milestones/README.md';s=path.read_text(encoding='utf-8')
s=s.replace('The manuscript is at revision 66, with its next full rewrite scheduled for milestone 76.',
 'The manuscript is at revision 76. Source and witness checks pass; the app compiler cannot start.')
entry='- [Milestone 76: paper revision and conditional arithmetic](76-paper-revision/README.md). Seven statements added, six fresh Lean checks; no new unconditional bound.\n\n'
if entry not in s:s=s.replace('- [Milestone 75:',entry+'- [Milestone 75:',1)
path.write_text(s,encoding='utf-8')
path=ROOT/'RESEARCH_LEDGER.md';s=path.read_text(encoding='utf-8')
if '## Milestone 76:' not in s:
    s+='\n## Milestone 76: paper revision and conditional arithmetic, 2 November 2026\n\n'+current+'\n\n'
    s+='The built-in compiler diagnostic and a frozen snapshot of successful case 7305 replay modules are saved. The final local theorem remains pending. The current interval is 191 through 235; 234 remains conditional. The written converse-emission argument is distinguished from the checked history invariant and soundness results.\n'
path.write_text(s,encoding='utf-8')
(ROOT/'handoff/README.md').write_text('''# Current continuation index

Latest checkpoint: [milestone 76](../milestones/76-paper-revision/README.md).
Both existing manuscript sources match, with authors and hyperlink settings
preserved. Checks pass for 123 statements, 180 labels and 13 snakes. Six new
Lean checks verify conditional arithmetic. The built-in compiler failed before
source compilation; its exact diagnostic is saved.

The project interval remains 191 through 235 edges. The target 234 depends on
six local shares, exact arbitrary-snake graph interpretation and full potential
replay. The conjecture 196 remains unresolved; no construction above 191 was
obtained here.

Case 7305 replay was active at the checkpoint. Inspect
`milestones/76-paper-revision/data/checkpoint.json`, its frozen successful-module
snapshot, and the actual process before acting. The saved tool session is 41012.
Do not start a duplicate completion driver. After refutation success, finish
full completion, geometry/reversal, axiom audit and case archival.

The [detailed handover](2026-11-02/START_HERE.md) retains definitions, environment,
earlier certificates and a continuation prompt. Its process and revision 66
status are historical; milestone 76 supersedes them. Historical manifests
identify their saved file versions.

Next work is to finish the active 012310 share-12 proof and assemble the exact
graph walk using the checked history, direction shifts, lookup and count-code
components. Complete the other five share targets and potential replay before
claiming 234. Recompile the same editor source when the app compiler can start.
The exact optimum remains the active goal.
''',encoding='utf-8')
print('Updated current manuscript and continuation pointers.')
