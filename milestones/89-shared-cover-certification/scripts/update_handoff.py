"""Record the frozen proof scope and the two continuing checks in current summaries."""
from pathlib import Path
import json

HERE = Path(__file__).resolve().parents[1]
ROOT = HERE.parents[1]
s = json.loads((HERE / 'data/proof-summary.json').read_text())
c = json.loads((HERE / 'data/checkpoint.json').read_text())
assert s['status'] == 'PASS_SHARED_COVER_INFRASTRUCTURE_PARTIAL_FINITE_BATCH'
assert s['theorem_audits'] == 28 and s['checked_geometric_classes'] == [0,1]
latest = ('Latest continuation: [milestone 89 checkpoint](milestones/89-shared-cover-certification/README.md) '
          'saves 28 Lean theorem audits, balanced geometric certificates for classes 0 and 1, '
          'and complete computational witness data for all 791 contexts. The sequential '
          '127-class batch continues; concrete context-witness equations remain open. '
          'History transport permits reuse of nonhistory witnesses. Case7302 has resumed '
          'past Check66 with a unique temporary output path. The paper stays at revision 86; '
          'the interval remains 191 through 235, with 234 conditional.')
for name in ['README.md','COLLABORATION.md']:
    p = ROOT / name
    t = p.read_text()
    a = t.index('Latest continuation:')
    b = t.index('\n\n',a)
    t = t[:a] + latest + t[b:]
    t = t.replace('During the replay, certify the 127 shared covers and context-specific witnesses using milestone 88, then identify the saved full-key rows and endpoint columns.',
                  'Continue the existing balanced-cover batch in milestone 89, then check its materialized context witnesses and identify the saved full-key rows and endpoint columns.')
    p.write_text(t,encoding='utf-8')

paragraph = '''Milestone 89 records 28 additional Lean theorem audits. History-free
witnesses transfer across bounded history IDs of the same direction. Shared
assembly pairs an equally long witness list with the fixed geometric box list,
including the three contexts whose history witness occupies position zero.
All 543,827 witness occurrences in 791 contexts have been materialized and
checked computationally, compressing to 211 aligned lists and 4,387 witness
constructors. Their complete concrete Lean validity equations remain open.

All 127 shared cover trees are generated and pointwise replayed on 5,925,312
class/code pairs. A balanced table lookup is proved equivalent to the original
list at every index and default. Its concrete graph table and the geometric
coverage equations for classes 0 and 1 pass Lean. The class-1 proof module took
51.828 seconds; earlier direct and array-box experiments were stopped without
completion after 685.187 and 475.312 seconds. These concurrent timings do not
give a controlled speed ratio. The sequential full-class batch is active in
tool session 23168; its frozen checkpoint covers only classes 0 and 1.

Case7302's original replay stopped at Check66 after its 300-second limit. A
first resume failed while replacing a stale temporary output. Both attempts
are preserved. The unique-output resume, tool session 14427, uses a 900-second
limit and has passed Check66 in 130.02 seconds. It reuses unchanged proof
sources and completed modules. Inspect actual processes before any restart.
Final geometry, reversal and the local-share audit remain pending.

'''
p = ROOT / 'handoff/CURRENT_STATUS.md'
t = p.read_text()
assert 'Milestone 89 records 28' not in t
t = t.replace('The remaining structural work is to supply', paragraph + 'The remaining structural work is to supply',1)
t = t.replace('only example\nwitnesses are stored with the common covers.',
              'milestone 88 stored example\nwitnesses, and milestone 89 supplies every context-specific list.')
t = t.replace('Milestone 88 contains the current shared handover versions and a later replay observation.',
              'Milestone 89 contains the current shared handover versions and later proof-process observations.')
t += (f"\nMilestone 89 freezes {c['case7302_distinct_successful_modules']} distinct successful replay modules, "
      f"including {len(c['case7302_new_successful_modules'])} newly observed since milestone 88. "
      f"The raw record contains {c['case7302_raw_successful_record_count']} successful rows because the inherited driver "
      'repeats composition rows when resumed. Duplicate rows are not counted as new modules.\n')
p.write_text(t,encoding='utf-8')

p = ROOT / 'handoff/NEXT_AGENT_PROMPT.md'
t = p.read_text().replace("milestone 88's coverage-pilot checkpoint", "milestone 89's shared-cover checkpoint")
a = t.index('The next finite task is to materialize context-specific witnesses')
b = t.index('After retained-edge membership, interpret',a)
t = t[:a] + '''Milestone 89 now supplies all context-specific witness data: 543,827
occurrences, 791 contexts, 211 aligned lists and 4,387 constructors. Do not
repeat materialization. The generic history transport, separate-list assembly
and leading-history helper are checked. Only three contexts use a history
witness, always at position zero. Reuse those exact orders and source indices.

Continue the EXISTING sequential balanced-cover process (tool session 23168,
script check_balanced_covers.py --classes all). At the frozen checkpoint,
classes 0 and 1 have successful original coverage equations and the round has
28 theorem audits. Its generic balanced lookup agrees with list lookup at all
indices/defaults; the concrete graph table is checked. The class-1 module
passed in about 52 seconds, excluding data compilation. The direct and array
lookup experiments were deliberately stopped without successful cover checks;
do not relaunch them. Inspect the actual process and active record before
resuming anything. Mutable run records are excluded from the saved manifest;
frozen observations and completed receipts specify its historical scope.

After the geometric batch, check concrete witness validity and context-class
assignment, using history transport for nonhistory witnesses. Equal witness
lists across different directions still need direction validity checks.
Then prove diagram membership implies the saved full-key rows and endpoint
columns. Keep both reference-catalogue premises explicit until discharged.
''' + t[b:]
t = t.replace('Its 127 semantic modules\nhave passed; preserve the current case and inspect its actual process before\nresuming the selected refutation replay.',
              'Its 127 semantic modules\nhave passed. The original replay timed out at Check66, and its first resume\nhit a temporary-output error. The unique-output resume is active in tool\nsession 14427 through milestones/89-shared-cover-certification/scripts/resume7302_unique.py; Check66 has\npassed. Preserve this process and inspect its actual state before any restart.')
p.write_text(t,encoding='utf-8')

p = ROOT / 'handoff/README.md'
t = p.read_text()
a = t.index('The current structural proof checkpoint is')
b = t.index('[Milestone 87]',a)
t = t[:a] + '''The current structural proof checkpoint is
[milestone 89](../milestones/89-shared-cover-certification/README.md), with
28 Lean theorem audits, checked balanced geometric covers for classes 0 and 1,
and complete computational witness lists for all 791 contexts. The sequential
127-class proof batch continues. Concrete witness validity, context assignment
and graph-row identities remain open. Use its
[checkpoint](../milestones/89-shared-cover-certification/data/checkpoint.json)
and [manifest](../milestones/89-shared-cover-certification/data/file-manifest.json)
for current handover versions and frozen observations of both proof processes.

[Milestone 88](../milestones/88-retention-diagram-certificate/README.md) supplies
the generic rejection-box argument and the complete direction-0/history-0
numeric-retention pilot. Its common-cover geometry is reused unchanged.

''' + t[b:]
t = t.replace("use milestone 88's manifest for their current versions.",
              "use milestone 89's manifest for their current versions.")
t = t.replace('Inspect the actual\nprocess before resuming; do not restart a live driver.',
              'Milestone 89 records the later timeout, output-path repair and unique-output\nresume past Check66. Inspect the actual process before resuming; do not restart\na live driver.')
p.write_text(t,encoding='utf-8')

p = ROOT / 'milestones/README.md'
t = p.read_text()
assert '- [Milestone 89:' not in t
t = t.replace('- [Milestone 88:',
              '- [Milestone 89: shared-cover checkpoint](89-shared-cover-certification/README.md). '
              '28 Lean audits; balanced geometric classes 0/1 checked, full batch active; all 791 context witnesses materialized computationally. '
              'History transport and lookup equivalences checked; no new numerical bound.\n\n- [Milestone 88:',1)
p.write_text(t,encoding='utf-8')

p = ROOT / 'RESEARCH_LEDGER.md'
t = p.read_text()
assert '## Milestone 89:' not in t
t += '''\n\n## Milestone 89: shared-cover checkpoint and balanced lookup

2 November 2026. This checkpoint records 28 Lean audits: four history-transport,
four separate-list assembly, two array-checker equality, five balanced lookup,
two general lookup-checker equality, three concrete graph-table and eight
concrete class 0/class 1 results. The full 127-class run remains active. All 127
trees are generated and pointwise replayed over 5,925,312 class/code pairs.

All 543,827 context-witness occurrences are materialized with original rule
indices, covering 791 contexts. Deduplication gives 211 aligned lists and 4,387
constructors. Only three occurrences use history, always at position zero.
The remaining witness equations, context assignment and graph interpretation
remain explicit. The source/data reviews preserve their own earlier snapshots.

Two lookup experiments were stopped without a cover proof after 685.187 and
475.312 seconds. Balanced class 1 succeeds in 51.828 seconds; class 0 in 66.453 seconds.
The experiment was concurrent, so no controlled speed ratio is claimed. The
graph compiler succeeded; an overly strict zero-axiom audit expectation was
corrected while preserving its successful output and original checker bytes.

Case7302 timed out at Check66, then a resume encountered a stale temporary
output error. The unique-output resume passes Check66 in 130.02 seconds and
continues through unchanged proof sources. Failed attempts are preserved.
Distinct successful modules are counted separately from repeated composition
rows. Bounds remain 191 through 235, with 234 conditional. The paper stays at
revision 86, next full revision 96. This checkpoint does not mark the full
geometric batch, the local share theorem or the overall goal complete.
'''
p.write_text(t,encoding='utf-8')
print('UPDATED_SEVEN_CURRENT_SUMMARIES',s['theorem_audits'],'audits')
