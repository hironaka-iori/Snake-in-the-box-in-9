"""Update continuation documents only from a completed milestone95 checkpoint."""
from pathlib import Path
import json,re
HERE=Path(__file__).resolve().parents[1];ROOT=HERE.parents[1]
c=json.loads((HERE/'data/checkpoint.json').read_text());assert c['status']=='PASS_COMPLETE_CONCRETE_HISTORY_CREDITS'
nw=len(c['checked_witness_classes']);ng=len(c['observed_geometry_classes']);na=c['new_lean_theorem_audits']
latest=(f'Latest continuation: [milestone 95 checkpoint](milestones/95-history-credit-integration/README.md) supplies all 69 geometric and eight capped word bounds for the 55 history-share rules. Their maximum is Lean-checked against the actual five-centre share sum, in the same environment as the defined graph. The source closure and adapters passed {na} theorem audits. '
        f'The frozen snapshot records {nw}/127 witness classes and {ng}/127 geometry classes. Bounds remain 191 through 235, with 234 conditional; paper revision 86 is unchanged.')
priority=('Next research priority: revise the existing paper at milestone 96, using standard notation and defining only essential recurring concepts. Then combine the remaining graph-weight components with the checked history credit and verify the complete potential on the defined graph, including conservative extra rows. Continue the witness and geometry batches. Preserve case7302\'s stopped Check1 replay until a controlled isolated test.')
for name in ['README.md','COLLABORATION.md']:
    p=ROOT/name;s=p.read_text();s,n=re.subn(r'^Latest continuation:.*$',latest,s,count=1,flags=re.M);assert n==1
    if name=='README.md':s,n=re.subn(r'^Next research priority:.*$',priority,s,count=1,flags=re.M);assert n==1
    p.write_text(s)
block=f'''## Milestone 95 checkpoint

All 55 saved history-share rules now have their concrete local bounds supplied.
The 69 geometric word bounds and eight stronger capped bounds pass Lean in a
compatible environment. The maximum of applicable bounds is checked against
the actual share sum at centres $r+4,\\ldots,r+8$, assuming $r+9\\le m$.
The final assembly imports the defined graph and has no remaining per-word
geometric premise. The exact 55-rule order, signatures, variants, caps and
credit values agree with the pinned model rows.

The selected source closure contains 46 ported modules. All proof text is
preserved except recorded import replacements and a consistent namespace
substitution. Five declaration conflicts with existing history support are
resolved without dropping a theorem or weakening its assumptions. The
source closure, transport, adapters and assembly passed {na} theorem audits.
This count includes auxiliary and extra instances retained in whole modules.

The [mathematical note](../milestones/95-history-credit-integration/mathematical-note.md)
explains the coordinate, centre and cap transfers without extra terminology.
Edge 58's nine-direction geometric bound and eleven-direction capped bound
are transferred separately. Alternative credits use maximum throughout.

The frozen snapshot records {nw}/127 witness classes and {ng}/127 geometry
classes. Sessions 13482 and 23168 continue unless their live records say
otherwise. Inspect actual processes before restarting. Case7302 remains
stopped after its Check1 timeout, with 649 successful modules and unchanged
replay sources.

The maintained interval remains $191\\le a(9)\\le235$ edges, with 234 conditional.
The upper bound retains contributor-proof and saved-audit evidence; a complete
independent rebuild remains pending. The current result supplies the history
part of the weight. Remaining weight components, retention premises, local
exclusions and the complete defined-graph potential remain separate.

Paper revision 86 and both source copies are unchanged. The next full revision
is due at milestone 96. Preserve authors and hyperlink settings, use standard
notation, and define only essential concepts that recur substantially.

'''
p=ROOT/'handoff/CURRENT_STATUS.md';s=p.read_text();a=s.index('## Milestone 94 checkpoint');b=s.index('## Result and evidence boundary');p.write_text(s[:a]+block+s[b:])
p=ROOT/'handoff/README.md';s=p.read_text();a=s.index('The current checkpoint is');b=s.index('[Milestone 93]',a)
s=s[:a]+'''The current checkpoint is
[milestone 95](../milestones/95-history-credit-integration/README.md), which
supplies all concrete history-share bounds and their maximum for actual snakes.
Its [checkpoint](../milestones/95-history-credit-integration/data/checkpoint.json)
and [manifest](../milestones/95-history-credit-integration/data/file-manifest.json)
preserve the checked sources, exact transformations and continuing batch state.
The complete global weight and potential assembly remains pending.

[Milestone 94](../milestones/94-history-share-dispatch/README.md) classifies
the exact compatible words and proves history/cap recognition.

'''+s[b:];p.write_text(s)
p=ROOT/'milestones/README.md';s=p.read_text();a=s.index('- [Milestone 94:');s=s[:a]+f'''- [Milestone 95: concrete history-credit integration](95-history-credit-integration/README.md). All 69 geometric and eight capped word bounds, 55 concrete rules and their maximum for actual snakes; {na} theorem audits including the ported source closure. No new numerical bound.

'''+s[a:];p.write_text(s)
p=ROOT/'RESEARCH_LEDGER.md';s=p.read_text();assert '## Milestone 95:' not in s
s+='\n\n## Milestone 95: concrete history-credit integration\n\n3 November 2026, Japan time. '+latest+'\n\n'+priority+'\n';p.write_text(s)
p=ROOT/'handoff/NEXT_AGENT_PROMPT.md';s=p.read_text();s=s.replace("Read the current handover, milestone 94's\nmathematical note, checkpoint and credit-provenance audit, then milestone 93's", "Read the current handover, milestone 95's\nmathematical note, checkpoint and source/literal audits, then milestone 94's\ncompatible-word classification and milestone 93's",1)
a=s.index('## Selected next mathematical task');b=s.index('## Reuse completed proof interfaces',a)
s=s[:a]+'''## Selected next mathematical task

Milestone 95 closes the concrete history-share obligations: 69 geometric and
eight capped adapters, all 55 RuleValid statements, and the maximum evaluator
bound for every actual snake with a fitting window. Reuse these receipts.
The final ConcreteRules95 module imports DefinedProofGraph and has no remaining
per-word geometric premise. The root literal audit independently checks all
saved credit values, caps, signature indices and variant indices.

The source ports use distinct module names and reuse the current share
declaration. CountPropagation65 is consistently renamed CountPropagationPort95
in eleven port files to avoid five declarations owned by HistoryCountSupport.
Every other non-import byte is preserved. Existing historical files are intact.
Do not mix legacy build paths back into this environment.

The paper revision is now due at milestone 96. Edit the existing editor source
in place, preserve authors and hypersetup, and synchronize its repository copy.
Explain the completed classification, fixed-model slope/range obstruction,
defined graph and concrete history credits in their logical order. Use ordinary
notation; introduce a definition only when essential and substantially reused.
Keep arbitrary-snake results separate from conditional graph conclusions.
Use the built-in compiler; preserve the source if the compiler cannot start.

After revision, assemble the remaining weight components and check the entire
potential on every row of the defined graph, including conservative extra rows.
An external-array certificate does not automatically transfer to this graph.
Retain all reference-catalogue and pending local-floor premises explicitly.
Continue witness and geometry batches; case7302 needs a controlled isolated
Check1 test before any fresh completion run.

'''+s[b:]
s=re.sub(r'The frozen milestone 94 checkpoint has \d+/127 witness classes, \d+/127 geometry',f'The frozen milestone 95 checkpoint has {nw}/127 witness classes, {ng}/127 geometry',s,count=1);p.write_text(s)
(HERE/'README.md').write_text(f'''# Milestone 95: concrete history-credit integration

All 55 saved history-share rules now bound the actual five-centre share sum.
Their 69 geometric word bounds and eight stronger capped bounds are supplied
by checked local theorems. The maximum of applicable credits is checked in
the same environment as the defined graph. No per-word geometric premise
remains in the final history-credit theorem.

The source closure, transport and assembly passed **{na} theorem audits**.
This includes auxiliary and extra local instances preserved in whole modules.
The 46 source ports change only recorded imports and one consistent namespace
token. An independent byte comparison checks those changes. A separate audit
matches every rule, word, credit and cap to the pinned model data.

Read the [mathematical note](mathematical-note.md), [checkpoint](data/checkpoint.json)
and [proof summary](data/proof-summary.json). The port plan records all original
and transformed sources; successful audit receipts pin the exact source, object,
log, checker snapshot and direct dependency bytes. Failed attempts are retained.
Build objects are local intermediates and are excluded from the saved manifest.

The frozen snapshot has {nw}/127 witness classes and {ng}/127 geometry classes.
Case7302 remains stopped at its preserved Check1 timeout. The interval remains
$191\\le a(9)\\le235$ edges, with 234 conditional. The 235 upper bound retains
contributor-proof and saved-audit evidence, pending a full independent rebuild.
Remaining weight components, retention premises and the global potential are
separate obligations. The next full paper revision is milestone 96.
''')
p=HERE/'mathematical-note.md';s=p.read_text();a=s.index('The saved audit receipts determine');b=s.index('This step supplies',a)
s=s[:a]+'''All 69 geometric word bounds and eight stronger capped bounds have now passed Lean. They supply every local premise in the 55-rule assembly, whose final theorem bounds the maximum contribution for every actual snake with a fitting window. The final assembly also imports the defined graph. An independent literal comparison checks the order, signatures, compatible words, caps and numerical credit values against the saved model.

'''+s[b:];p.write_text(s)
print('UPDATED_COMPLETED_MILESTONE95_HANDOVER',na,nw,ng)
