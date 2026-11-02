"""Update current handover with the completed comparison and selected next method."""
from pathlib import Path
import json
HERE = Path(__file__).resolve().parents[1]
ROOT = HERE.parents[1]
c = json.loads((HERE/'data/checkpoint.json').read_text())
s = json.loads((HERE/'data/proof-summary.json').read_text())
assert s['theorem_audits']==8 and s['observed_geometry_classes']==list(range(20))
assert c['case7302_distinct_successful_modules']==493
latest = ('Latest continuation: [milestone 91 checkpoint](milestones/91-reference-shape-reuse/README.md) '
          'checks certified reference-pattern reuse and the same six-direction membership result, '
          'with eight new Lean audits. The completed direct/cache comparison establishes no consistent '
          'speed advantage. Use the direct balanced-lookup checker for the 507 base witness jobs '
          'and three history heads. The snapshot records geometric classes 0 through 19 and 493 '
          'distinct successful case7302 modules; both runs continue. Bounds remain 191 through 235, '
          'with 234 conditional. Paper revision 86 is unchanged.')
for name in ['README.md','COLLABORATION.md']:
    p=ROOT/name; t=p.read_text(); a=t.index('Latest continuation:'); b=t.index('\n\n',a)
    t=t[:a]+latest+t[b:]
    t=t.replace('Continue the existing balanced-cover batch and case7302 replay. Use milestone 90 to test normalized reference-shape reuse before the full witness batch, then close context assignment and full-key endpoints.',
                'Continue both existing proof runs. Milestone 91 completes the cache comparison; expand the direct checker to the saved witness jobs, then close context assignment and full-key endpoints.')
    p.write_text(t,encoding='utf-8')
paragraph='''Milestone 91 completes the reference-pattern reuse experiment. Three generic
Lean audits certify bounded cache lookup with complete descriptor equality;
five concrete audits check 156 patterns, two count lists, all six assignments
and the same membership conclusion as the direct pilot. The original 3,732
reference entries and 108 nonreference entries remain covered. The two direct
theorems are rechecked for timing and are not new results.

Direct proof trials took 18.812 and 37.875 seconds; cached trials took 24.203
and 28.016 seconds. Cached timings include descriptor correspondence and
assembly. Additional generic and data setup took 46.125 and 45.219 seconds.
Two other Lean processes were active throughout; the small concurrent sample
does not establish a speed advantage. The selected method for the full witness
batch is the direct balanced-lookup checker. Do not repeat the cache benchmark
without a materially changed representation or a new reason.

The milestone91 snapshot records geometric classes 0 through 19 and 493
distinct successful case7302 modules. Both existing processes continue; the
full geometry batch and local-share theorem remain pending. Use the newer
snapshot and actual process state when continuing. The complete context
assignment, full-key membership and endpoint identities remain open.

'''
p=ROOT/'handoff/CURRENT_STATUS.md';t=p.read_text()
assert 'Milestone 91 completes' not in t
t=t.replace('The remaining structural work is to supply',paragraph+'The remaining structural work is to supply',1)
t=t.replace('Milestone 90 contains the current shared handover versions and later proof-process observations.',
            'Milestone 91 contains the current shared handover versions and later proof-process observations.')
p.write_text(t,encoding='utf-8')
p=ROOT/'handoff/NEXT_AGENT_PROMPT.md';t=p.read_text()
t=t.replace("milestone 90's witness checkpoint","milestone 91's completed cache experiment")
a=t.index('The next bounded task is a same-class reference-shape reuse pilot.')
b=t.index('After retained-edge membership, interpret',a)
t=t[:a]+'''Milestone 91 has completed that same-class experiment. It checks a certified
shape-table substitution and all concrete descriptor matches for 156 patterns
serving the 3,732 reference entries. The 108 nonreference entries use unchanged
compatibility. Two count lists serve the six jobs. Eight new audits pass;
the direct source is byte-identical to milestone 90 and its two prior theorems
are rechecked. The final membership hypotheses and conclusion match exactly.

Direct trials took 18.812/37.875 seconds; cached trials 24.203/28.016 seconds.
Cached proof time includes every descriptor and assembly check, with extra
generic/data setup of 46.125/45.219 seconds. Two other proof processes were
active, so no consistent performance advantage is established. Select the
direct balanced-lookup method for the full witness batch. Preserve the sound
cache theorem, but do not repeat this benchmark without a changed representation.

The next task is to expand the direct checker to the saved 507 base jobs and
three separate history heads, using original list orders and same-length
checks. The 788 head-free contexts use history transport. Class 85's two heads
share one tail; class 89 has the remaining head. Keep heads at position zero.
Combine validity with the completed geometric class certificates, then certify
the complete context assignment and saved full-key rows and endpoints.
Keep both reference-catalogue premises explicit until discharged.

Milestone 91 observes geometric classes 0 through 19 and 493 distinct successful
case7302 modules, with no final share audit. The process handles remain 23168
and 14427. Inspect their actual current state before resuming anything; the
cached-pilot handle 70247 is terminal and successful. Do not restart a live job.

'''+t[b:]
p.write_text(t,encoding='utf-8')
p=ROOT/'handoff/README.md';t=p.read_text();a=t.index('The current structural proof checkpoint is');b=t.index('[Milestone 89]',a)
t=t[:a]+'''The current checkpoint is
[milestone 91](../milestones/91-reference-shape-reuse/README.md), with eight
new Lean audits for certified reference-pattern reuse and its concrete pilot.
The completed timing comparison gives no consistent speed advantage; continue
with the direct balanced-lookup witness method. Its
[checkpoint](../milestones/91-reference-shape-reuse/data/checkpoint.json) and
[manifest](../milestones/91-reference-shape-reuse/data/file-manifest.json)
record current shared-file versions and both continuing proof runs.

[Milestone 90](../milestones/90-context-witness-certificates/README.md) supplies
the checked direct pilot, exact lookup tables, witness factorization, the
507-job plan and complete computational factor profile. Reuse that data.

'''+t[b:]
t=t.replace("use milestone 90's manifest for their current versions.","use milestone 91's manifest for their current versions.")
p.write_text(t,encoding='utf-8')
p=ROOT/'milestones/README.md';t=p.read_text();assert '- [Milestone 91:' not in t
t=t.replace('- [Milestone 90:','- [Milestone 91: certified reference-pattern reuse](91-reference-shape-reuse/README.md). Eight new Lean audits; complete same-case cache pilot; no consistent timing advantage. Use direct checks for the full witness batch.\n\n- [Milestone 90:',1)
p.write_text(t,encoding='utf-8')
p=ROOT/'RESEARCH_LEDGER.md';t=p.read_text();assert '## Milestone 91:' not in t
addition='''\n\n## Milestone 91: certified reference-pattern reuse

2 November 2026. Eight new Lean audits check generic bounded shape substitution
and the same six-case membership result using 156 cached patterns for 3,732
reference occurrences. Catalogue, placement and index guards, complete descriptor
equality and zip lengths are checked. The 108 nonreference occurrences retain
their original compatibility tests. The direct source is byte-identical to90;
its two theorem audits are repeated for timing and add no new results.

Direct trials took 18.812/37.875 seconds; cached trials24.203/28.016 seconds,
including descriptor and assembly checks. Generic/data setup adds46.125/45.219
seconds. Concurrent load was not controlled. No speed advantage is established,
so the next full batch will use the direct balanced-lookup checker and the
saved507-job/three-head plan. Exact trial logs and hashes are preserved.

The checkpoint observes geometric classes0 through19 and493 distinct successful
case7302 modules. Both jobs continue. Bounds remain191 through235, with234
conditional; paper revision 86 is unchanged. The full research goal remains open.
'''
# Keep numbers legible in the new paragraph.
for a,b in [('to90','to 90'),('trials24','trials 24'),('adds46','adds 46'),('saved507','saved 507'),
            ('classes0','classes 0'),('through19','through 19'),('and493','and 493'),('remain191','remain 191'),
            ('through235','through 235'),('with234','with 234'),('revision 86','revision 86')]:
    addition=addition.replace(a,b)
t+=addition
p.write_text(t,encoding='utf-8')
print('UPDATED_SEVEN_SUMMARIES',8,'new audits; direct checker selected')
