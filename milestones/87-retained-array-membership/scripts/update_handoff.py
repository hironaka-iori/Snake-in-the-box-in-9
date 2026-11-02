"""Update only current project summaries after the milestone evidence gate."""
from pathlib import Path
import json
HERE=Path(__file__).resolve().parents[1];ROOT=HERE.parents[1]
s=json.loads((HERE/'data/proof-summary.json').read_text())
assert s['status']=='PASS_RETENTION_INTERFACES_AND_COMPUTATIONAL_COVERAGE'
n=s['theorem_audits']
latest=f'Latest continuation: [milestone 87](milestones/87-retained-array-membership/README.md) proves executable numeric retention and conditional saved-edge indexing, with {n} new Lean theorem audits. An independent comparison matches all 36,904,896 compatible candidate keys and all 4,947,008 stored edges. The retention-cover definition isolates the remaining finite coverage certificate. Full keys must be preserved: 206,589 endpoint pairs have two edges. The two reference-catalogue premises, concrete Lean coverage, weights and potential remain separate obligations. The paper stays at revision 86; the interval remains 191 through 235, with 234 conditional.'
for name in ['README.md','COLLABORATION.md']:
    p=ROOT/name;t=p.read_text();a=t.index('Latest continuation:');b=t.index('\n\n',a)
    t=t[:a]+latest+t[b:]
    t=t.replace('During the replay, close the 1,378-key reference union and exact retained-array membership.',
        'During the replay, certify the finite retention cover and endpoint columns using the numeric predicate and conditional assembly from milestone 87. The 1,378-key reference union is checked under two explicit catalogue premises.')
    p.write_text(t,encoding='utf-8')
paragraph=f'''Milestone 87 adds {n} Lean theorem audits across four modules. It combines
all retention families, defines an executable bounded numeric predicate and
proves that every fitting actual snake step passes it under the same two
reference-catalogue premises. A retention cover contains every accepted key;
exact table equality is a stronger sufficient condition. Given finite coverage
and the two endpoint-column identities, the checked assembly assigns an
in-bounds saved edge to every step of the complete actual state walk.

Two independent executable audits verify exact accepted-code equality on all
36,904,896 compatible candidate keys, the 4,947,008 saved rows, their ordering
and every endpoint. All 791 compatible blocks match; all 37,084 incompatible
blocks are empty. Full candidate keys are unique, while 206,589 endpoint pairs
have multiplicity two. Keep edge identity as (direction, history, count code).
The Python checks do not discharge the concrete Lean coverage or endpoint
premises, and do not certify equality with the executable Lean predicate.
The 791 blocks share only 127 distinct count-code sets. A shared six-way
decision diagram with 3,981 nonterminal nodes reconstructs every set and
block exactly, occupying 29,924 compressed bytes. Its coverage implication
still needs a Lean proof; this is the next finite certificate target.
The combined imports reuse hash-checked existing proof objects; no complete
dependency rebuild is claimed.

'''
p=ROOT/'handoff/CURRENT_STATUS.md';t=p.read_text()
a=t.index('The remaining retained-edge work is');b=t.index('Every three-ID credit',a)
t=t[:a]+paragraph+'''The remaining structural work is to supply the two closed reference
catalogue proofs and a concrete Lean retention cover with endpoint-column
identities. The universal conditional indexing argument is now supplied.
'''+t[b:]
t=t.replace('its manifest identifies the current shared handover versions.',
    'its manifest identifies that revision. Milestone 87 contains the current shared handover versions and a later replay observation.')
p.write_text(t,encoding='utf-8')
p=ROOT/'handoff/NEXT_AGENT_PROMPT.md';t=p.read_text()
t=t.replace("milestone 86's paper checkpoint and milestone 85's proof README.",
    "milestone 87's structural proof checkpoint and milestone 86's paper checkpoint.")
t=t.replace('In the meantime, use the checked conditional\ninterface to supply the exact retained-array index. After retained-edge membership, interpret',
    '''Milestone 87 now supplies the executable numeric predicate, actual-step
acceptance and conditional saved-edge/walk assembly. Reuse those checks. Its
RetentionCover requires only that every accepted key is stored; exact equality
is sufficient but stronger. Certify this concrete finite coverage and the
endpoint-column identities in Lean. The independent Python equality has already
passed on all 36,904,896 compatible candidate keys, but it does not certify the
Lean predicate's finite table. Preserve full keys because 206,589 endpoint
pairs have two edges. Use the saved membership decision diagram: 127 distinct
count-code sets, 3,981 nonterminal nodes, all blocks independently reconstructed.
Its complete compressed data and generator are in milestone87. Prove numeric
acceptance implies acceptance by the assigned diagram root, then certify its
row indexing and endpoint columns. A complementary certificate could cover
omitted codes by proved forbidden regions. These proof designs remain open.
After retained-edge membership, interpret''')
p.write_text(t,encoding='utf-8')
p=ROOT/'handoff/README.md';t=p.read_text()
t=t.replace('The latest manuscript and handover checkpoint is','The latest manuscript checkpoint is',1)
t=t.replace('current paper, shared handover versions and replay observation.',
    'paper revision and its historical handover and replay observation.',1)
marker='The current proof checkpoint is'
a=t.index(marker);b=t.index('[Milestone 84]',a)
t=t[:a]+f'''The current structural proof checkpoint is
[milestone 87](../milestones/87-retained-array-membership/README.md), with {n}
Lean theorem audits, executable numeric retention and conditional saved-walk
indexing. Exact computational coverage passes on all 36,904,896 compatible
candidate keys. Concrete Lean coverage and endpoint-column certificates remain
open. Use its [checkpoint](../milestones/87-retained-array-membership/data/checkpoint.json)
and [manifest](../milestones/87-retained-array-membership/data/file-manifest.json)
for the current shared handover versions and replay observation.

The preceding reference checkpoint is
[milestone 85](../milestones/85-reference-catalogue-union/README.md): 103 audits,
1,378 keys and retention under two explicit catalogue-refutation premises.

'''+t[b:]
t=t.replace('The remaining retained-edge work covers those closed proofs and\nthe exact array index; credit interpretation follows.',
    'Milestone 87 supplies conditional indexing. The remaining structural work\nis the closed reference proofs and concrete finite coverage/endpoint certificates;\ncredit interpretation follows.')
t=t.replace("use milestone 86's manifest for their current versions.","use milestone 87's manifest for their current versions.")
p.write_text(t,encoding='utf-8')
p=ROOT/'milestones/README.md';t=p.read_text();marker='- [Milestone 86:'
assert '- [Milestone 87:' not in t
t=t.replace(marker,f'- [Milestone 87: retention covers and saved-edge indexing](87-retained-array-membership/README.md). {n} Lean theorem audits; actual numeric acceptance and conditional whole-walk indexing; exact computational coverage of 36,904,896 compatible keys. Concrete Lean finite certificates remain open; bounds unchanged.\n\n'+marker,1)
p.write_text(t,encoding='utf-8')
p=ROOT/'RESEARCH_LEDGER.md';t=p.read_text();assert '## Milestone 87:' not in t
t+=f'''\n\n## Milestone 87: retention covers and saved-edge indexing

2 November 2026. {n} fresh Lean theorem audits combine all retention families,
prove an executable bounded predicate true for each actual snake step and
assemble a complete saved state walk under explicit finite coverage and
endpoint-column premises. The two reference-catalogue premises remain.
The retention-cover definition isolates the weaker inclusion sufficient for
membership; exact generator equality and duplicate-free key indexing have
generic checked interfaces. No proof identifies an edge only by its endpoints.

Independent executable reconstruction agrees on 36,904,896 compatible candidate
keys, 791 compatible blocks and every one of the 4,947,008 saved rows. All
37,084 incompatible blocks are empty. Ordered full keys are unique, but
206,589 endpoint pairs have multiplicity two. Every stored endpoint agrees
with the source formula. The arrays remain computationally audited rather
than supplied as a closed Lean finite coverage certificate. Weight validity
and full potential replay are still separate. Source/object hashes for the
combined inherited support are checked; that closure is reused, not rebuilt.

The paper remains revision 86, with the next scheduled full revision at96.
The maintained interval is191 through235;234 remains conditional. Case7302
continues through its existing driver without duplicate replay. The new
checkpoint preserves its current successful rows, logs and process observation.
'''
p.write_text(t,encoding='utf-8')
print('UPDATED_SEVEN_CURRENT_SUMMARIES',n,'Lean audits')
