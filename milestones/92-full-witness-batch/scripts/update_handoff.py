"""Publish the frozen milestone92 checkpoint without changing manuscript bytes."""
from pathlib import Path
import json
HERE=Path(__file__).resolve().parents[1];ROOT=HERE.parents[1]
c=json.loads((HERE/'data/checkpoint.json').read_text());s=json.loads((HERE/'data/proof-summary.json').read_text())
assert s['context_assignment_checked'] and s['assignment_positions']==37875
n=len(s['checked_witness_classes']);ng=len(s['observed_geometry_classes']);nr=c['case7302_distinct_successful_modules']
lite_audits=sum(r['theorem_audits'] for r in s['modules'] if r['module'].startswith('ContextAssignmentLite'))
graph_status='three conditional theorem audits passed' if s['defined_graph_bridge_checked'] else 'source prepared; compiler check pending'
handle=c['witness_batch_tool_session']
paragraph=f'''Milestone 92 checks the complete source-compatible context assignment over
37,875 direction/history pairs, including the three history-dependent class
overrides and exact agreement with the saved block classes and roots. This
check enumerates no count codes. The frozen checkpoint has {s['theorem_audits']}
Lean theorem audits, {n} of 127 concrete witness classes, {ng} geometric classes
and {nr} distinct successful case7302 modules. These are snapshot counts.

The all-class witness process is active in tool session {handle}, alongside
geometry session 23168 and replay session 14427. Inspect actual process state
before any resume; do not duplicate live jobs. All 507 base jobs and three
leading history witnesses are generated and independently reviewed. The final
family assembly requires every class receipt and is queued after the batch.
The exact checkpoint states whether that final theorem has passed.

The chosen next proof object is the graph defined directly from diagram-accepted
full keys, with endpoints computed from each key. This avoids a separate identity
with external row and endpoint arrays if all weight and potential certificates
are checked on the defined graph. Keep the two reference-catalogue premises,
pending local shares, credit interpretation and complete potential explicit.
The interval remains 191 through 235 edges, with 234 conditional. The contributor
upper-bound proof still needs a complete independent rebuild. Paper revision 86
and its three authors and hyperlink settings are unchanged; the next full
revision is scheduled for milestone 96.
'''
latest=(f'Latest continuation: [milestone 92 checkpoint](milestones/92-full-witness-batch/README.md) '
        f'checks all 37,875 context positions and exact saved class/root selection. '
        f'The snapshot records {n}/127 witness classes, {ng}/127 geometric classes and {nr} successful '
        'case7302 modules. The complete witness batch is running. Bounds remain 191 through 235, '
        'with 234 conditional; paper revision 86 is unchanged.')
for name in ['README.md','COLLABORATION.md']:
    p=ROOT/name;t=p.read_text();a=t.index('Latest continuation:');b=t.index('\n\n',a)
    t=t[:a]+latest+t[b:]
    t=t.replace('Continue both existing proof runs. Milestone 91 completes the cache comparison; expand the direct checker to the saved witness jobs, then close context assignment and full-key endpoints.',
                'Continue the existing witness, geometry and case7302 processes. Context assignment is checked; complete the class family and check weights and potentials on the graph defined from accepted keys.')
    p.write_text(t,encoding='utf-8')
p=ROOT/'handoff/CURRENT_STATUS.md';t=p.read_text();assert '## Milestone 92 checkpoint' not in t
a=t.index('\n\n')+2;t=t[:a]+'## Milestone 92 checkpoint\n\n'+paragraph+'\nEarlier milestone entries below describe their recorded scopes. Use the milestone92\ncheckpoint for current proof status and process observations.\n\n'+t[a:]
t=t.replace('Milestone 91 contains the current shared handover versions and later proof-process observations.',
            'Milestone 92 contains the current shared handover versions and later proof-process observations.')
p.write_text(t,encoding='utf-8')
p=ROOT/'handoff/NEXT_AGENT_PROMPT.md';t=p.read_text()
t=t.replace("milestone 91's completed cache experiment","milestone 92's context assignment and active witness checkpoint")
t=t.replace('Certify this concrete finite coverage and the\nendpoint-column identities in Lean.',
            'Milestone 92 now supplies a checked conditional graph definition whose\ncoverage and endpoints follow from its construction. Use that defined graph\nfor subsequent weight and potential checks; an exact external-array comparison\nis optional if no external-only certificate is transferred.')
t=t.replace('The remaining two premises are AllRefuted6K235 and AllRefuted236;',
            'The two remaining reference-catalogue premises are AllRefuted6K235 and AllRefuted236;')
a=t.index('The next task is to expand the direct checker');b=t.index('After retained-edge membership, interpret',a)
t=t[:a]+paragraph+'''\nUse the existing sequential checker with --classes all --wait-for-geometry;
the final CloseBatch module is scheduled after all 127 classes. Reuse valid
receipts with matching source and dependency hashes. A saved source without
a successful receipt is pending. Class 85 has two leading history witnesses;
class 89 has one. Preserve their positions and the original base lists.
The witness runner checks other Lean processes' private memory before launch
and waits above its configured threshold. This is a scheduling guard, not a
bound on later concurrent peaks. Interrupted active jobs retain their lock
until their actual child-process state has been inspected.

'''+t[b:];p.write_text(t,encoding='utf-8')
p=ROOT/'handoff/README.md';t=p.read_text();a=t.index('The current checkpoint is');b=t.index('[Milestone 90]',a)
t=t[:a]+'''The current checkpoint is
[milestone 92](../milestones/92-full-witness-batch/README.md), with checked
source-compatible context assignment and a continuing all-class witness batch.
Its [checkpoint](../milestones/92-full-witness-batch/data/checkpoint.json) and
[manifest](../milestones/92-full-witness-batch/data/file-manifest.json) preserve
exact current evidence and three continuing proof-process observations.

Milestone 91 completed the reference-pattern experiment. No consistent speed
advantage was established; the current batch uses direct balanced lookup.

'''+t[b:]
t=t.replace("use milestone 91's manifest for their current versions.","use milestone 92's manifest for their current versions.")
p.write_text(t,encoding='utf-8')
p=ROOT/'milestones/README.md';t=p.read_text();assert '- [Milestone 92:' not in t
t=t.replace('- [Milestone 91:',f'- [Milestone 92: context assignment and full witness batch](92-full-witness-batch/README.md). All 37,875 context positions checked; {n}/127 witness classes at snapshot; complete sequential run active.\n\n- [Milestone 91:',1)
p.write_text(t,encoding='utf-8')
p=ROOT/'RESEARCH_LEDGER.md';t=p.read_text();assert '## Milestone 92:' not in t
t+='\n\n## Milestone 92: context assignment and full witness batch\n\n2 November 2026. '+paragraph
p.write_text(t,encoding='utf-8')
readme=f'''# Milestone 92: context assignment and full witness batch

The complete source-compatible context assignment passes Lean. It selects the
exact recorded class and root for every accepted bounded direction/history pair.
The remaining class proofs are running as one sequential batch.

{paragraph}
## Checked statements and definitions

The [mathematical note](mathematical-note.md) separates a base witness job,
a context assignment and the class membership family. Four generic audits
prove base-list extraction, history transport and restoration of a leading
history witness. Three context-assignment audits prove source projection and
generic selection. Six further audits check the finite selector and derive
the corresponding retained-key statements. The lightweight finite checker and
its equality bridge supply {lite_audits} additional audits, preserving the original
assignment predicate while avoiding repeated source/history table lookups.
Completed class receipts contribute five audits per ordinary class and six per class with a leading history witness.

The selector covers 505 direction indices and 75 histories. The 791 compatible
contexts use a 505-entry default-class vector and three overrides. It agrees with the
saved block-to-class and class-to-root tables, including every original key.
Count-code bounds and target-history compatibility remain in the original
retention predicate. The concrete class checks preserve equal list lengths,
all entry positions, all reference guards and all three separate history heads.
The six class-1 jobs reuse their already checked validity theorem.

Generated sources cover all 127 classes, 507 base validity jobs and 210 base
lists. [Independent review](audit/full-batch-review.md) reconstructed all
357,820 base entries, 791 contexts and three restored heads. Its checker review
covers the preserved version before final-assembly scheduling was added.
The complete family theorem is generated in CloseBatch and will only be
reported checked after its successful receipt. Sources alone are insufficient.

The snapshot has **{s['theorem_audits']} theorem audits**, **{n} checked witness
classes**, **{s['checked_contexts']} checked contexts** and
**{s['checked_base_jobs']} checked base jobs**. See the
[proof summary](data/proof-summary.json) for exact module names and counts.
Printed axioms are subsets of propext, Classical.choice and Quot.sound.
Checked sources contain no sorry, admit or native_decide. Existing dependency
objects are reused and pinned; their full dependency closure was not rebuilt.

## Graph defined from accepted keys

DefinedProofGraph has status: **{graph_status}**. Its graph lists bounded full
keys accepted by the diagram at the saved block class, with missing blocks
rejected. Its endpoint arrays are defined by the existing source and target
functions. Under explicit class-family, assignment and reference premises,
these conditional statements supply coverage, endpoint identities and an actual
snake walk in that graph.

This is the selected continuation. It removes a separate external-array
identity obligation only if every later weight and potential certificate is
checked on the defined graph. See the [independent mathematical review](audit/defined-proof-graph-option.md).
Existing certificates about the external arrays cannot be transferred without
that check. The full graph family and the numerical bound remain unresolved.

## Reproduction and process state

```text
python scripts/check_batch.py --classes all --wait-for-geometry
python scripts/verify_saved.py --verify
```

The first command is a resume entry point. Inspect the active record and actual
processes before using it. One process owns the batch lock, reuses matching
successful receipts and waits for missing geometry. The current handle is
{handle}. Geometry handle 23168 and replay handle 14427 remain separate.
Mutable records and unfinished logs are excluded from the manifest. The
snapshot may lag later progress. Build objects are preserved locally.

The first complete context-assignment attempt reached its 900-second limit
without a finite-check result. Its child process had about 12.03 GB private
allocation; private allocation differs from resident memory. The surviving
owned child was identified and terminated after the wrapper timed out. Exact
source, checker, empty log and process evidence are preserved. The completed
certificate uses the later partitioned lightweight check and bridge; the failed attempt
is not counted as a theorem audit.

The first lightweight monolithic attempt was also interrupted under resource
pressure, without a successful finite-check receipt. Its exact snapshots are
preserved under data/repairs. The final partitioned checks retain the same
assignment predicate and source/history ranges.

The witness runner waits when other Lean processes exceed its pre-launch
private-memory threshold. This reduces avoidable overlap but cannot bound
later memory peaks. Dependency source/object/log/receipt pins are checked
again after waiting and after compilation. Interrupted active jobs retain
their lock for actual-process inspection before any resume.

An initial global-data compile failed because it opened an unused namespace
without importing its defining module. The unused open was removed; the
failed source, log, generator and repaired metadata are retained under
data/repairs. No witness entries changed. Checker versions are also preserved;
the current runner checks generated source hashes before every dispatch.

The [checkpoint](data/checkpoint.json) records process observations, source
and paper hashes, pending premises and the next task. The
[manifest](data/file-manifest.json) pins the saved evidence and shared handover.
No new numerical upper bound is claimed.
'''
(HERE/'README.md').write_text(readme,encoding='utf-8')
print('UPDATED_SEVEN_SUMMARIES_AND_README',s['theorem_audits'],n,ng,nr)
