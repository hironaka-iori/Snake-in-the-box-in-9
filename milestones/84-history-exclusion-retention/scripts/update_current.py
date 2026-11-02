"""Update the current handover without modifying historical milestone evidence."""
from pathlib import Path
HERE=Path(__file__).resolve().parents[1];ROOT=HERE.parents[1]
def save(path,text):path.write_text(text,encoding='utf-8')
latest=('Latest continuation: [milestone 84](milestones/84-history-exclusion-retention/README.md) '
    'proves that every actual snake passes all three history-exclusion guards. Eight modules '
    'passed 38 Lean audits, including complete three-signature realization and a fresh replay '
    'of the adapted count proofs. An independent comparison checks the exact isolated builder '
    'loop. Case 7302 continues under its existing proof driver and remains pending. '
    'The maintained interval remains 191 through 235; see [the current handover](handoff/README.md).')
priority=('Next research priority: continue the existing case 7302 replay and complete its '
    'geometry, reversal and final audit before integration. During the replay, close the '
    '1,378-key reference union and exact retained-array membership. The three history exclusions '
    'are complete. Credit interpretation, full potential replay and all five pending local '
    'share targets remain obligations of the proposed 234 certificate.')
for rel in ['README.md','COLLABORATION.md']:
    path=ROOT/rel;lines=path.read_text().splitlines()
    for i,line in enumerate(lines):
        if line.startswith('Latest continuation:'):lines[i]=latest
        if line.startswith('Next research priority:'):lines[i]=priority
    save(path,'\n'.join(lines)+'\n')
path=ROOT/'milestones/README.md';text=path.read_text()
entry=('- [Milestone 84: three-history retention](84-history-exclusion-retention/README.md). '
    '38 Lean audits prove that every actual snake survives all three history guards; '
    'complete signature realization and encoded count transport are checked. No numerical bound changes.\n\n')
if entry not in text:text=text.replace('- [Milestone 83:',entry+'- [Milestone 83:',1)
save(path,text)
path=ROOT/'RESEARCH_LEDGER.md';text=path.read_text();title='## Milestone 84: complete three-history exclusion transport'
if title not in text:text+='\n\n'+title+'\n\n'+(
    '2 November 2026. Eight modules passed 38 Lean audits. Three emitted history IDs identify '
    'the actual overlapping nine-direction windows; each exclusion signature has exactly one '
    'compatible induced eleven-direction word. The existing count lower bounds three then '
    'contradict digit caps two at the correct positions. The final theorem applies to every '
    'actual snake and fitting step without an unresolved local certificate premise. The small '
    'helper and count proofs were replayed in the current window environment after an older '
    'import closure caused duplicate declarations. Definitions and proof bodies were retained.\n\n'
    'Independent complete enumeration covers all 11,162 canonical induced eleven-words. '
    'The actual isolated builder loop agrees on 37,875 history/direction pairs with six '
    'uniform count vectors each, followed by all 46,656 count codes for each of the three '
    'active pairs. These are filter tests, not full-graph edge counts. The reference union, '
    'retained-array index, credit interpretation, potential replay and five local share targets '
    'remain. Case 7302 continues under the existing driver. The interval remains 191 through '
    '235; paper revision 76 is unchanged and the next full revision is 86.\n')
save(path,text)
path=ROOT/'handoff/CURRENT_STATUS.md';text=path.read_text()
text=text.replace('Milestones 77 through 83','Milestones 77 through 84')
text=text.replace('forty-rule retention, a cycle obstruction and the pending next share certificate',
    'forty-rule retention, three-history retention, a cycle obstruction and the pending next share certificate')
old=('The remaining retained-edge work is the 1,378-key reference union, three\n'
     'history exclusions and the exact retained-array index.')
new=('Milestone 84 closes all three history-exclusion guards, with 38 audits across\n'
     'eight modules. The actual emitted IDs recover each unique eleven-direction\n'
     'word, and its count lower bound three excludes the digit cap two. All three\n'
     'count proofs and five small helper lemmas were checked afresh against the\n'
     'current window bridge. An exact isolated-loop comparison covers all 37,875\n'
     'history/direction pairs and all count codes for the three active guards.\n\n'
     'The remaining retained-edge work is the 1,378-key reference union and\n'
     'the exact retained-array index.')
if old in text:text=text.replace(old,new)
save(path,text)
path=ROOT/'handoff/NEXT_AGENT_PROMPT.md';text=path.read_text()
text=text.replace('and milestone 83\'s README and exact checkpoint. Milestones 81 and 82 record the preceding results.',
    "and milestone 84's README and exact checkpoint. Milestone 83 preserves the active case 7302 proof sources.")
text=text.replace('The next assembly task is to instantiate the 1,378-key reference\nunion and three history exclusions, then supply the exact retained-array index.',
    'Milestone 84 closes all three history exclusions with 38 Lean audits; reuse\nits complete signature recognition and count transport. The next assembly\ntask is to instantiate the 1,378-key reference union, then supply the exact\nretained-array index.')
text=text.replace('milestones 77 through 83','milestones 77 through 84')
save(path,text)
path=ROOT/'handoff/README.md';text=path.read_text()
intro=('The current proof checkpoint is [milestone 84](../milestones/84-history-exclusion-retention/README.md).\n'
    'Its 38 Lean audits close all three history-exclusion guards for actual snakes.\n'
    'Use its [checkpoint](../milestones/84-history-exclusion-retention/data/checkpoint.json)\n'
    'and [manifest](../milestones/84-history-exclusion-retention/data/file-manifest.json)\n'
    'for current evidence, handover versions and a later observation of the active replay.\n\n')
if intro not in text:text=text.replace('The active local-certificate task is',intro+'The active local-certificate task is',1)
text=text.replace('The current [checkpoint](../milestones/83-','The case-preparation [checkpoint](../milestones/83-')
text=text.replace('The latest optimisation checkpoint is [milestone 82]','The preceding cycle-obstruction checkpoint is [milestone 82]')
text=text.replace('The latest proof checkpoint is\n[milestone 81]','The preceding short-rule proof checkpoint is\n[milestone 81]')
text=text.replace("use milestone 83's manifest for their current versions.","use milestone 84's manifest for their current versions.")
text=text.replace('recovered short filters. The remaining retained-edge work covers the reference\nunion, history exclusions and exact retained-array membership.',
    'recovered short filters. Milestone 84 closes all three history exclusions.\nThe remaining retained-edge work covers the reference union and exact\nretained-array membership.')
text=text.replace('recovered short filters. The remaining retained-edge work covers the reference\nunion, three history exclusions and\nthe exact array index;',
    'recovered short filters. Milestone 84 closes all three history exclusions.\nThe remaining retained-edge work covers the reference union and\nthe exact array index;')
text=text.replace('hash-matched during milestone 81.','hash-matched during milestone 84.')
save(path,text)
print('Updated current records for milestone84; case7302 remains pending')
