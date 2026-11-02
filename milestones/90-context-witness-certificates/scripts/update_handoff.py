"""Publish the frozen milestone90 scope in the existing local handover."""
from pathlib import Path
import json

HERE = Path(__file__).resolve().parents[1]
ROOT = HERE.parents[1]
s = json.loads((HERE / 'data/proof-summary.json').read_text())
c = json.loads((HERE / 'data/checkpoint.json').read_text())
assert s['status'] == 'PASS_WITNESS_PILOT_AND_GENERIC_FACTORIZATION'
n = s['theorem_audits']
classes = s['observed_geometry_classes']
assert classes == list(range(len(classes)))
geometric = f"classes 0 through {classes[-1]}"
latest = (f'Latest continuation: [milestone 90 checkpoint](milestones/90-context-witness-certificates/README.md) '
          f'records {n} Lean theorem audits, exact balanced witness tables and a six-direction '
          'retained-code membership result. Generic witness factorization is checked. The full '
          '791-context assignment remains open. A saved plan reduces it to 507 base witness jobs '
          'and three history heads; a computational profile identifies reusable shape and count '
          f'tests. The continuing geometric batch has checked {geometric} at this snapshot. '
          'Case7302 continues. Bounds remain 191 through 235, with 234 conditional; paper revision 86 is unchanged.')
for name in ['README.md', 'COLLABORATION.md']:
    p = ROOT / name
    t = p.read_text()
    a = t.index('Latest continuation:')
    b = t.index('\n\n', a)
    t = t[:a] + latest + t[b:]
    t = t.replace('Continue the existing balanced-cover batch in milestone 89, then check its materialized context witnesses and identify the saved full-key rows and endpoint columns.',
                  'Continue the existing balanced-cover batch and case7302 replay. Use milestone 90 to test normalized reference-shape reuse before the full witness batch, then close context assignment and full-key endpoints.')
    p.write_text(t, encoding='utf-8')

paragraph = f'''Milestone 90 adds {n} Lean theorem audits. Balanced lookups preserve the exact
505-direction and 1,378-reference tables, including out-of-range defaults.
The class-1 certificate now gives retained-code membership for directions
1, 3, 307, 308, 310 and 312, for every bounded history under the original
predicate. Its six assignments contain 3,840 witness checks, and the proof
module passed in 21.125 seconds, excluding data and shared table checks.

Compatibility and count conditions are separated by a checked general
identity. A normalized direction-pattern expression permits reference keys
with the same shape and count-list length to share the shape calculation.
Concrete compressed descriptors and their full assembly remain unchecked.
The computational plan has 507 base validity jobs and three history heads,
covering all 791 contexts. Its 357,823 entries contain 15,353 distinct shape
tests and 2,651 count tests, together with 508 outer and 2,329 catalogue
guards. Every saved direct/factored Boolean comparison passes. These are
valid saved entries; the experiment alone proves no general equivalence or
speed improvement. Test reference-shape reuse on the same six-job pilot
before expanding it throughout the finite batch.

At the milestone90 snapshot, the existing geometric process has successful
receipts for {geometric}; its full 127-class batch remains active.
The case7302 replay has {c['case7302_distinct_successful_modules']} distinct successful modules
({c['case7302_raw_successful_record_count']} raw successful rows). Its local-share theorem and
final audit remain pending. Both live processes must be inspected before
any restart. The checkpoint contains immutable observations and a delta log
archive. The upper-bound and reference-premise limitations remain unchanged.

'''
p = ROOT / 'handoff/CURRENT_STATUS.md'
t = p.read_text()
assert 'Milestone 90 adds' not in t
t = t.replace('The remaining structural work is to supply', paragraph + 'The remaining structural work is to supply', 1)
t = t.replace('Milestone 89 contains the current shared handover versions and later proof-process observations.',
              'Milestone 90 contains the current shared handover versions and later proof-process observations.')
p.write_text(t, encoding='utf-8')

p = ROOT / 'handoff/NEXT_AGENT_PROMPT.md'
t = p.read_text().replace("milestone 89's shared-cover checkpoint", "milestone 90's witness checkpoint")
a = t.index('After the geometric batch, check concrete witness validity')
b = t.index('After retained-edge membership, interpret', a)
t = t[:a] + f'''Milestone 90 checks exact balanced direction/reference lookups and six class-1
direction assignments, at indices 1, 3, 307, 308, 310 and 312. The resulting
membership theorem holds for every q < 75 under the original numericKeep
predicate; it does not certify all context assignments. The proof module
took 21.125 seconds. Reuse the source/object/log receipts and two witness lists.
The round adds {n} audits, including general compatibility/count factorization.

The saved job plan reconstructs all 791 contexts as 507 base validity jobs
and three separate history heads. Do not regenerate the materialization or
discard the head positions. The exact computational factor profile identifies
15,353 shape tests and 2,651 count tests in 357,823 entries. Reference keys
dominate; their 337,485 catalogue-indexed shape calls reduce to 12,560 normalized
shape expressions. Full compatibility still retains catalogue guards, so
caching it by key index alone misses this reduction. Use WitnessFactors'
normalized shape definitions and prove descriptor/source correspondences.

The next bounded task is a same-class reference-shape reuse pilot. Include
all correspondence and assembly checks in the comparison; no speedup is yet
measured. Then expand concrete witness certification, certify context-to-class
assignment, and connect diagram membership to full-key rows and endpoints.
Keep both reference-catalogue premises explicit until discharged.

The newer geometric observation in milestone90 covers {geometric};
the two continuing process handles remain 23168 and 14427. The case7302
snapshot contains {c['case7302_distinct_successful_modules']} distinct successful modules and no final
share audit. Use current actual process state, not an older session count,
before deciding whether to resume. The saved snapshots are historical.

''' + t[b:]
p.write_text(t, encoding='utf-8')

p = ROOT / 'handoff/README.md'
t = p.read_text()
a = t.index('The current structural proof checkpoint is')
b = t.index('[Milestone 88]', a)
t = t[:a] + f'''The current structural proof checkpoint is
[milestone 90](../milestones/90-context-witness-certificates/README.md), with
{n} Lean theorem audits, a six-direction retained-code membership pilot,
exact balanced witness lookups and general witness factorization. The saved
791-context plan and factor profile remain computational beyond this pilot.
Use its [checkpoint](../milestones/90-context-witness-certificates/data/checkpoint.json)
and [manifest](../milestones/90-context-witness-certificates/data/file-manifest.json)
for current shared-file versions and frozen observations of both live jobs.

[Milestone 89](../milestones/89-shared-cover-certification/README.md) supplies
shared cover geometry and materialized context witnesses. Its sequential
127-class run continues; milestone90 observes {geometric} completed.
The historical milestone89 snapshot claimed only classes 0 and 1.

''' + t[b:]
t = t.replace("use milestone 89's manifest for their current versions.", "use milestone 90's manifest for their current versions.")
p.write_text(t, encoding='utf-8')

p = ROOT / 'milestones/README.md'
t = p.read_text()
assert '- [Milestone 90:' not in t
t = t.replace('- [Milestone 89:',
              '- [Milestone 90: witness compatibility and counts](90-context-witness-certificates/README.md). '
              f'{n} Lean audits; six-direction membership pilot, exact lookup tables and generic factorization; '
              '507 base jobs plus three history heads planned. No new bound.\n\n- [Milestone 89:', 1)
p.write_text(t, encoding='utf-8')

p = ROOT / 'RESEARCH_LEDGER.md'
t = p.read_text()
assert '## Milestone 90:' not in t
t += f'''\n\n## Milestone 90: witness compatibility and count conditions

2 November 2026. {n} Lean audits check generic lookup substitutions, exact
balanced direction/reference tables, six class-1 witness assignments and
their numeric-retention implication, and general witness factorization.
The concrete pilot covers 3,840 validity entries across six directions and
extends to every bounded history under the original predicate. Its proof
module took 21.125 seconds. Full context assignment remains open.

The all-context plan contains 507 base validity jobs and three separate
history heads. Its 357,823 entries share 15,353 normalized shape tests and
2,651 count tests, with 508 outer and 2,329 catalogue guards. Every saved
entry comparison agrees. Reference keys account for 338,697 entries and
only 12,560 normalized shape tests. This is computational evidence for a
same-class sharing experiment; concrete descriptor equality and assembly
are still required, and no timing improvement is claimed.

The checkpoint observes {geometric} completed in the continuing
127-class geometry run and {c['case7302_distinct_successful_modules']} distinct successful modules in
case7302. Exact logs, dependency pins and live-state snapshots are saved.
Neither process is restarted. Bounds remain 191 through 235, with 234
conditional. Paper revision 86 is unchanged; the next rewrite is due at 96.
'''
p.write_text(t, encoding='utf-8')
print('UPDATED_SEVEN_SUMMARIES', n, 'audits;', geometric)
