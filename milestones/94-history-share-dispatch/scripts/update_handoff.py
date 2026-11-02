"""Update current continuation documents from milestone94's frozen checkpoint."""
from pathlib import Path
import json,re
HERE=Path(__file__).resolve().parents[1];ROOT=HERE.parents[1]
c=json.loads((HERE/'data/checkpoint.json').read_text());nw=len(c['checked_witness_classes']);ng=len(c['observed_geometry_classes'])
latest=("Latest continuation: [milestone 94 checkpoint](milestones/94-history-share-dispatch/README.md) "
        "checks all 55 history-share signatures with 73 Lean theorem audits. Their exact compatible sets contain "
        "69 words: 41 signatures are unique and 14 have two variants. Actual-window recognition and generic "
        "count-cap transport are checked. Every needed local credit has an identified historical theorem; "
        "concrete instantiation in a compatible import environment and maximum-credit dispatch remain. "
        f"The frozen snapshot records {nw}/127 witness classes and {ng}/127 geometry classes. "
        "Bounds remain 191 through 235, with 234 conditional; paper revision 86 is unchanged.")
priority=("Next research priority: connect the existing per-word share theorems to the current share definition. "
          "Start with the credit-2 rule FamilyCharge67.G000, using a uniquely named compatible support module "
          "and the checked history classification; then extend to all 69 geometric and eight capped bounds. "
          "Old ShareFrame and current LocalWindowShareBridge declare identical coreShare text under different "
          "module ownership, and five instance-module names collide. Resolve these imports and recheck the "
          "selected source closure before combining applicable credits by maximum. Continue the witness and "
          "geometry batches. Preserve case7302's stopped Check1 replay until a controlled isolated test.")
for name in ['README.md','COLLABORATION.md']:
    p=ROOT/name;s=p.read_text();s,n=re.subn(r'^Latest continuation:.*$',latest,s,count=1,flags=re.M);assert n==1
    if name=='README.md':s,n=re.subn(r'^Next research priority:.*$',priority,s,count=1,flags=re.M);assert n==1
    p.write_text(s)
block=f'''## Milestone 94 checkpoint

All 55 history-share signatures now have checked exact compatible sets. Their
69 canonical eleven-direction words form 41 singleton sets and 14 two-word sets.
The 73 Lean audits cover every finite table, reverse inclusion, distinct signatures,
actual emitted-window membership, centre offsets and numeric count-cap transport.
The eight older representative-only rules are all unique. Counts below six retain
their exact cap meaning; the saturated symbol is not treated as an exact count.

The [mathematical note](../milestones/94-history-share-dispatch/mathematical-note.md)
defines compatible configurations. The [provenance map](../milestones/94-history-share-dispatch/audit/credit-provenance.md)
finds all 69 geometric word bounds and eight stronger capped bounds in existing
local proofs. Concrete instantiation remains. Legacy and current share modules
declare the same core share name, and five instance-module names collide. The
inspected core share definition text is identical; the import ownership must be
resolved and the chosen source closure rechecked in one environment.

The selected next task is a compatible credit-2 instance for FamilyCharge67.G000,
followed by all geometric/capped instances and the maximum-credit evaluator.
Edge 58's uncapped credit 6 comes from a nine-direction suffix; its capped credit 12 uses
an eleven-direction theorem. Preserve these different transfers.

The frozen snapshot has {nw}/127 witness classes and {ng}/127 geometry classes.
Their existing sessions 13482 and 23168 continue. Case7302 remains stopped after
its Check1 timeout, with 649 successful modules and unchanged replay sources.
Inspect actual processes before restarting any job.

The maintained interval remains $191\\le a(9)\\le235$ edges, with 234 conditional.
The upper bound retains contributor-proof and saved-audit evidence; a complete
independent rebuild remains pending. Paper revision 86 and both source copies
are unchanged. The next full paper revision is scheduled for milestone 96.

Milestone 93's optimality of the three fixed-model slope/range comparisons still
applies. Stronger graph restrictions, credits, boundary accounting or endpoint
information are needed to improve those comparisons. Earlier entries below
retain their historical scopes; the current frozen checkpoint is milestone 94.

'''
p=ROOT/'handoff/CURRENT_STATUS.md';s=p.read_text();a=s.index('## Milestone 93 checkpoint');b=s.index('## Result and evidence boundary');p.write_text(s[:a]+block+s[b:])
p=ROOT/'handoff/README.md';s=p.read_text();a=s.index('The current checkpoint is');b=s.index('[Milestone 92]',a)
s=s[:a]+'''The current checkpoint is
[milestone 94](../milestones/94-history-share-dispatch/README.md), with 73 Lean
audits classifying all 55 history-share signatures and checking actual-window
and count-cap dispatch. Its [checkpoint](../milestones/94-history-share-dispatch/data/checkpoint.json)
and [manifest](../milestones/94-history-share-dispatch/data/file-manifest.json)
preserve the exact results, local-credit provenance and continuing batch observations.
The next task is compatible concrete credit instantiation and maximum dispatch.

[Milestone 93](../milestones/93-defined-graph-potential/README.md) proves the
joint slope/range comparison and preserves the case7302 timeout evidence.

'''+s[b:];p.write_text(s)
p=ROOT/'milestones/README.md';s=p.read_text();a=s.index('- [Milestone 93:');s=s[:a]+'''- [Milestone 94: complete history-share configurations](94-history-share-dispatch/README.md). 73 Lean audits; all 55 signatures, 69 exact compatible words, actual-window and capped dispatch. Existing local credits are mapped; compatible concrete instantiation and maximum dispatch remain. No new numerical bound.

'''+s[a:];p.write_text(s)
p=ROOT/'RESEARCH_LEDGER.md';s=p.read_text();assert '## Milestone 94:' not in s
s+='\n\n## Milestone 94: complete history-share configurations\n\n3 November 2026, Japan time. '+latest+'\n\n'+priority+'\n\n'
s+='Two complete numerical enumerations agree with the generated lists. Lean checks both coverage and validity of all listed words. The source audit identifies 77 historical local theorems across 29 modules, with 42 reused geometry results checked separately. The compatible local-credit port remains to be compiled; no new local share bound or global numerical bound is claimed.\n';p.write_text(s)
p=ROOT/'handoff/NEXT_AGENT_PROMPT.md';s=p.read_text()
s=s.replace("Read the current handover, milestone 93's\nmathematical note, checkpoint and two independent audits, then milestone 92's", "Read the current handover, milestone 94's\nmathematical note, checkpoint and credit-provenance audit, then milestone 93's\nfixed-model comparison and milestone 92's",1)
a=s.index('## Selected next mathematical task');b=s.index('## Reuse completed proof interfaces',a)
s=s[:a]+'''## Selected next mathematical task

Milestone 94 completes the compatible-word classification for all 55 history
share signatures. All 69 variants are checked, with 41 singleton and 14 two-word
sets. Actual emitted-window membership and generic numeric cap transport pass
Lean. Reuse these 73 audits; do not repeat the finite cover calculations.

Instantiate the per-word geometric and capped premises in the current proof
environment. The provenance map identifies all 69 geometric word theorems and
eight stronger capped theorems. No extra local geometric lower-bound claim is
missing from this model, but their combined interpretation is still pending.

The first concrete target is FamilyCharge67.G000.in_snake, credit 2 for the
single-word rule with edge label 2000. Port only the needed generic support to
the current LocalWindowShareBridge, under distinct module names, preserving
definitions and theorem statements. Then check coordinate transfer, emitted
word membership and the five centres. Expand only after this instance passes.

Legacy ShareFrame and current LocalWindowShareBridge independently declare
coreShare and related names. The coreShare definition text agrees; importing
both owners is the issue. Selected Edge007/010/011/045/057 module names also
collide across old milestones. Preserve the old files and receipts; use uniquely
named compatible sources and audit their full selected dependency closure.
Reordering old paths or renaming compiled objects does not validate this port.

The eleven-word start is $s=r-2$. Its credited offsets 6 through 10 become
$r+4,\\ldots,r+8$. A six-count cap at position $k$ concerns $r+k+3$, hence
the local ten-entry bounds-list index $4+k$. All current caps are below six;
the saturated symbol still means $[6,21]$. Rule edge 58 has an uncapped credit 6 from
SplitShare62.E27 on the canonical final nine directions, while its capped credit 12
uses CountPropagation65.E058 on the eleven-word. Keep those transfers separate.

After the individual bounds, define the exact contribution of each rule: zero
without an emitted signature, geometric credit on a match, and the maximum
with capped credit when every cap holds. Prove the maximum over all 55 rules
is bounded by the same five-centre share sum. Keep the full history/direction/
count key and match the pinned model's literal signatures, caps and credits.

Finally combine the remaining weight components and check the entire potential
on the graph defined from accepted keys, including any conservative extra rows.
An external-array certificate does not transfer merely because its graph was
used to construct the diagram. Reference-catalogue and pending local-floor
premises remain explicit until separately discharged.

'''+s[b:]
s=re.sub(r'The frozen milestone 93 checkpoint has \d+/127 witness classes, \d+/127 geometry',f'The frozen milestone 94 checkpoint has {nw}/127 witness classes, {ng}/127 geometry',s,count=1)
p.write_text(s)
print('UPDATED_SEVEN_HANDOVER_FILES',nw,ng)
