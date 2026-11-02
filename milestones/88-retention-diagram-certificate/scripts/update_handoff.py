"""Update the seven current summaries after the milestone evidence gate."""
from pathlib import Path
import json

HERE = Path(__file__).resolve().parents[1]
ROOT = HERE.parents[1]
summary = json.loads((HERE / 'data/proof-summary.json').read_text())
checkpoint = json.loads((HERE / 'data/checkpoint.json').read_text())
assert summary['status'] == 'PASS_GENERIC_BOX_COVER_AND_ONE_KERNEL_PILOT'
assert summary['theorem_audits'] == 26

latest = ('Latest continuation: [milestone 88](milestones/88-retention-diagram-certificate/README.md) '
          'adds 26 Lean theorem audits for rejection boxes, six-way coverage and a concrete '
          'direction-0/history-0 pilot. Lean checks its 375 witnesses and coverage tree. '
          'Computationally, all 791 contexts admit covers grouped into 127 membership classes, '
          'with 82,659 shared box occurrences; all-context Lean certification remains open. '
          'The two reference premises, saved-row and endpoint identification, weights and '
          'potential remain separate obligations. The paper stays at revision 86; the '
          'interval remains 191 through 235, with 234 conditional.')
for name in ['README.md', 'COLLABORATION.md']:
    p = ROOT / name
    t = p.read_text()
    a = t.index('Latest continuation:')
    b = t.index('\n\n', a)
    t = t[:a] + latest + t[b:]
    t = t.replace(
        'During the replay, certify the finite retention cover and endpoint columns using the numeric predicate and conditional assembly from milestone 87.',
        'During the replay, certify the 127 shared covers and context-specific witnesses using milestone 88, then identify the saved full-key rows and endpoint columns.')
    p.write_text(t, encoding='utf-8')

paragraph = '''Milestone 88 adds 26 Lean theorem audits. A rejection box is a product of
six count intervals with a checked original-rule witness. A six-way coverage
tree proves that every vector is either accepted by a membership diagram or
contained in one of these boxes. The generic theorem proves numeric retention
implies diagram acceptance; its actual-snake specialization retains the two
reference-catalogue premises. The direction-0/history-0 pilot supplies the
finite premises: Lean checks all 375 witnesses, the coverage equation and the
resulting retained-code theorem. It has 723 distinct tree nodes and 6,123
accepted codes; the three concrete proof checks took 92.594 seconds.

The computational reconstruction still matches every saved block. Moreover,
all 127 membership classes have a common box cover available across every
context of that class. Pruning yields 82,659 class-box occurrences, compared
with 356,548 direct direction-box occurrences. This suggests 127 shared
geometric checks. Each context still needs its own rule witnesses; only example
witnesses are stored with the common covers. The full all-context Lean
certificate and identification with the saved full-key rows remain open.
These generic and pilot results do not give a new global bound.

'''
p = ROOT / 'handoff/CURRENT_STATUS.md'
t = p.read_text()
t = t.replace('Its coverage implication\nstill needs a Lean proof; this is the next finite certificate target.',
              'Milestone 88 supplies the generic coverage implication and one concrete\nchecked context; the complete finite certificate remains open.')
marker = 'The remaining structural work is to supply'
assert 'Milestone 88 adds 26' not in t
t = t.replace(marker, paragraph + marker, 1)
t = t.replace('Milestone 87 contains the current shared handover versions and a later replay observation.',
              'Milestone 88 contains the current shared handover versions and a later replay observation.')
t += (f"\nMilestone 88 freezes {len(checkpoint['case7302_successful_rows'])} successful case7302 replay rows, "
      f"including {len(checkpoint['case7302_new_successful_modules'])} newly observed since milestone 87. "
      'The log archive and hash scopes are explicit. This is a partial snapshot; '
      'the final local-share theorem remains pending.\n')
p.write_text(t, encoding='utf-8')

p = ROOT / 'handoff/NEXT_AGENT_PROMPT.md'
t = p.read_text().replace("milestone 87's structural proof checkpoint", "milestone 88's coverage-pilot checkpoint")
a = t.index('Its complete compressed data and generator are in milestone87.')
b = t.index('After retained-edge membership, interpret', a)
t = t[:a] + '''Its complete compressed data and generator are in milestone87.
Milestone 88 supplies generic rejection boxes, witnessed exclusions, a
six-way coverage checker and the theorem from numeric retention to diagram
membership, with 26 theorem audits including a concrete pilot. Reuse these
checks; direction 0/history 0 already passes all 375 witness checks and its
coverage equation. Do not treat this pilot as all-context coverage.

The next finite task is to materialize context-specific witnesses for the
127 common covers in milestone88's max-gain payload. Their geometry covers
all rejected codes in every class computationally; the selected covers have
82,659 class-box occurrences. Generate and check one coverage tree per class,
then each context's witness list. The current class data contains example
witnesses only. Run measured sequential batches; the pilot's proof check took
about 93 seconds, excluding data compilation. Retain failures and exact source,
object and log hashes. Then certify the link from each diagram root to the
recorded full-key rows and the two endpoint columns. Do not identify weighted
edges solely by endpoints.
''' + t[b:]
p.write_text(t, encoding='utf-8')

p = ROOT / 'handoff/README.md'
t = p.read_text()
a = t.index('The current structural proof checkpoint is')
b = t.index('The preceding reference checkpoint is', a)
t = t[:a] + '''The current structural proof checkpoint is
[milestone 88](../milestones/88-retention-diagram-certificate/README.md), with
26 Lean theorem audits for rejection boxes, coverage trees and one concrete
direction-0/history-0 certificate. Its 375 witnesses and coverage equation
are checked. All-context coverage remains open; a computational common-cover
construction reduces the geometric work to 127 membership classes.
Use its [checkpoint](../milestones/88-retention-diagram-certificate/data/checkpoint.json)
and [manifest](../milestones/88-retention-diagram-certificate/data/file-manifest.json)
for current handover versions and the latest preserved replay observation.

[Milestone 87](../milestones/87-retained-array-membership/README.md) supplies
executable numeric retention and conditional saved-walk indexing, with 27
audits and exact computational coverage of 36,904,896 compatible candidate
keys. Saved-row and endpoint-column certificates remain necessary.

''' + t[b:]
t = t.replace("use milestone 87's manifest for their current versions.",
              "use milestone 88's manifest for their current versions.")
t = t.replace('Milestone 87 supplies conditional indexing. The remaining structural work',
              'Milestone 87 supplies conditional indexing, and milestone 88 supplies the\ngeneric coverage argument and one checked context. The remaining structural work')
p.write_text(t, encoding='utf-8')

p = ROOT / 'milestones/README.md'
t = p.read_text()
assert '- [Milestone 88:' not in t
t = t.replace('- [Milestone 87:',
              '- [Milestone 88: rejection boxes and a checked coverage pilot](88-retention-diagram-certificate/README.md). '
              '26 Lean theorem audits; generic rejection/coverage chain and direction-0/history-0 certificate. '
              'All 127 common covers are computationally exact; all-context certification and saved-row identification remain open. Bounds unchanged.\n\n- [Milestone 87:', 1)
p.write_text(t, encoding='utf-8')

p = ROOT / 'RESEARCH_LEDGER.md'
t = p.read_text()
assert '## Milestone 88:' not in t
t += '''\n\n## Milestone 88: rejection boxes and a checked coverage pilot

2 November 2026. The round adds 26 Lean theorem audits: box-prefix containment,
digit reconstruction, four rejection-witness families, six-way coverage,
numeric-retention assembly and three concrete pilot checks. Two additional
data modules compile with no theorem audits. Every printed theorem uses only
standard axioms; the pilot coverage equation uses none. Inherited objects
are reused without a complete dependency rebuild.

For direction 0 and history 0, all 375 witnesses and the coverage tree pass
kernel checks. The retained-code membership theorem follows. There are 723
distinct tree nodes, 11,869 expanded visits and 6,123 accepted codes. The
concrete proof module takes 92.594 seconds; graph and pilot data compilation
take 96.219 and 46.203 seconds respectively.

Computational box reconstruction agrees on all 791 compatible blocks and
4,947,008 rows. Maximum-uncovered selection retains 356,548 direct occurrences,
1,369 fewer than the preserved baseline. Every selected direct box has a
private code; no minimum-size cover is claimed. The more useful reduction
finds a common geometric cover in all 127 membership classes, with 82,659
class-box occurrences. Context-specific witness lists for those common
covers still need materialization and Lean checks.

All-context finite coverage, diagram-to-row identification, endpoint columns,
the two reference-catalogue premises, credit interpretation and full potential
replay remain open. The bounds remain 191 through 235, with 234 conditional.
The paper stays at revision 86, next scheduled revision 96. The existing
case7302 replay continues; its partial logs are preserved in a delta snapshot
with reused and freshly hashed objects distinguished.
'''
p.write_text(t, encoding='utf-8')
print('UPDATED_SEVEN_CURRENT_SUMMARIES', summary['theorem_audits'], 'Lean audits')
