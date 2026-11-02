"""Record case7302 progress without admitting an unfinished local theorem."""
from pathlib import Path
HERE=Path(__file__).resolve().parents[1];ROOT=HERE.parents[1]
save=lambda p,t:p.write_text(t,encoding='utf-8',newline='\n')
latest=('Latest continuation: [milestone 83](milestones/83-012034-share-certificate/README.md) '
    'pursues the count-free 012034 share-20 theorem. Its 121 clause shards and semantic assembly '
    'have passed, giving 127 checked modules before refutation replay. The local theorem remains '
    'pending. Adding only this proposed floor gives exact conditional finite mean 9259/19, scaled '
    'potential range 11301 at denominator 19, and integer comparison 235. A separate verifier checks '
    'all 4,947,008 edges; three Lean audits check the arithmetic. The maintained interval remains '
    '191 through 235. See [the current handover](handoff/README.md).')
priority=('Next research priority: finish the existing case 7302 replay and its geometry, reversal '
    'and source/axiom audit, then integrate it only after the final local theorem passes. Inspect '
    'the live process before resuming; do not duplicate it. Case 7307 is the following local target. '
    'All five pending local share targets remain obligations of the full 234 certificate.')
for name in ['README.md','COLLABORATION.md']:
    path=ROOT/name;lines=path.read_text().splitlines()
    for i,line in enumerate(lines):
        if line.startswith('Latest continuation:'):lines[i]=latest
        if line.startswith('Next research priority:'):lines[i]=priority
    save(path,'\n'.join(lines)+'\n')
path=ROOT/'milestones/README.md';text=path.read_text()
entry=('- [Milestone 83: 012034 share-20 certificate in progress](83-012034-share-certificate/README.md). '
       '127 semantic modules checked; local refutation replay and final theorem pending. Exact '
       'single-target conditional mean 9259/19 still gives integer comparison 235.\n\n')
if entry not in text:text=text.replace('- [Milestone 82:',entry+'- [Milestone 82:',1)
save(path,text)
path=ROOT/'RESEARCH_LEDGER.md';text=path.read_text();heading='## Milestone 83: 012034 share-20 preparation and conditional pressure'
if heading not in text:
    text+='\n\n'+heading+'\n\n2 November 2026. '
    text+=('Case 7302 is being promoted from the saved native refutation to a Lean local theorem. '
      'The target is 20 on shape 012034 with all five counts in [0,21] and no cycle cuts. Independent '
      'review checks all 99,818 native clauses, 15,446 selected core clauses, compact renaming and '
      'generated Lean literals. All 121 semantic shards and their assembly passed, for 127 modules. '
      'Compact LRAT generation, original export simulation and reduced export simulations passed; final '
      'Lean replay are recorded separately in the live checkpoint. The local theorem remains '
      'pending until geometry, reversal and the complete source/axiom audit pass.\n\n'
      'The exact finite comparison adding only the unproved 012034 floor 20 raises 1,043,097 edges '
      'over the completed-share model. Its mean is 9259/19, scaled range 11301, and bound '
      '20965613/89059, giving 235. A separate verifier checks every edge and an attaining 19-cycle; '
      'three Lean audits check conditional arithmetic. This target alone cannot reach 234 under '
      'the current budget, even at range zero. The global interval and completed local catalogue '
      'are unchanged. Paper revision 76 remains current; next full revision 86.\n')
save(path,text)
path=ROOT/'handoff/README.md';text=path.read_text()
paragraph=('The active local-certificate task is [milestone 83](../milestones/83-012034-share-certificate/README.md):\n'
    'case 7302, the 012034 share-20 target. Its clause interpretation and assembly\n'
    'have passed; the refutation replay and final local theorem remain pending.\n'
    'The current [checkpoint](../milestones/83-012034-share-certificate/data/checkpoint.json)\n'
    'and [manifest](../milestones/83-012034-share-certificate/data/file-manifest.json)\n'
    'record the exact saved evidence and process observation. Inspect the actual\n'
    'process before resuming; do not restart a live driver. Earlier manifests\n'
    'identify their historical versions of shared handover files.\n\n')
if paragraph not in text:text=text.replace('The latest optimisation checkpoint is',paragraph+'The latest optimisation checkpoint is',1)
text=text.replace('Use its [current saved-file manifest]', 'Its [saved-file manifest]')
text=text.replace('to verify the present checkpoint and shared handover files.', 'records that completed round and its then-current handover files.')
text=text.replace("use milestone 82's manifest for their current versions.","use milestone 83's manifest for their current versions.")
save(path,text)
path=ROOT/'handoff/CURRENT_STATUS.md';text=path.read_text()
paragraph=('Milestone 83 is actively checking case 7302. All 121 semantic shards and\n'
    'their combined interpretation passed, giving 127 modules before refutation\n'
    'replay. The generated compact refutation, original export simulation and\n'
    'reduced export simulations passed. Selected Lean replay and final geometry\n'
    'remain pending. Inspect its saved checkpoint and actual\n'
    'process before restarting anything.\n\n'
    'Adding only this unproved floor gives exact finite mean 9259/19 and scaled\n'
    'potential range 11301 at denominator 19. Its bound 20965613/89059 still\n'
    'rounds down to 235. It raises 1,043,097 weights over the completed-share\n'
    'model. All-edge checking and three Lean arithmetic audits do not discharge\n'
    'the added local premise or the full graph interpretation.\n\n')
if 'Milestone 83 is actively checking case 7302.' not in text:text=text.replace('## Proof interfaces and remaining work\n',paragraph+'## Proof interfaces and remaining work\n',1)
save(path,text)
path=ROOT/'handoff/NEXT_AGENT_PROMPT.md';text=path.read_text()
text=text.replace('and the milestone 81 and 82 READMEs and exact checkpoints.',
    'and milestone 83\'s README and exact checkpoint. Milestones 81 and 82 record the preceding results.')
start=text.index('For the next optimisation check, prioritize case 7302') if 'For the next optimisation check, prioritize case 7302' in text else text.index('The active task is case 7302 (012034, share 20).')
end=text.index('Avoid repeating the failed monolithic coverage check;',start)
text=text[:start]+('The active task is case 7302 (012034, share 20). Its 127 semantic modules\n'
    'have passed; preserve the current case and inspect its actual process before\n'
    'resuming the selected refutation replay. Do not bootstrap or regenerate\n'
    'checked sources. Complete geometry, reversal and the source/axiom audit,\n'
    'then archive, restore, integrate and recompute using the completed premise.\n'
    'Until that gate passes, the new mean 9259/19 is conditional on this one\n'
    'unproved local floor. It still gives integer comparison 235.\n\n'
    'Case 7307 (012340, share 16) is the following local target. Milestone 82\n'
    'shows that these two proposed floors raise one saved witness to 497; that\n'
    'does not determine the full graph mean. Bonuses vanishing whenever all six\n'
    'stored symbols are below six cannot improve the old graph mean 483 under\n'
    'the same budget. Keep all five pending target cases explicit until checked.\n\n')+text[end:]
text=text.replace('milestones 77 through 82','milestones 77 through 83')
save(path,text)
print('Updated current records; case7302 remains pending')
