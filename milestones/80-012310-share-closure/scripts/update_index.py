"""Refresh current status after case7305, integration and comparison all pass."""
from pathlib import Path
import json
HERE=Path(__file__).resolve().parents[1];ROOT=HERE.parents[1];OLD=ROOT/'milestones/73-countfree-share-catalogue'
c=json.loads((HERE/'data/checkpoint.json').read_text())
assert c['status']=='PASS_012310_SHARE_CLOSURE_AND_MODEL_COMPARISON'
def save(p,s):p.write_text(s,encoding='utf-8',newline='\n')
new=('Latest continuation: [milestone 80](milestones/80-012310-share-closure/README.md) '
     'completes the count-free 012310 share-12 theorem: 465 modules, 100 local audits and '
     '35 combined-catalogue audits. Five local share targets remain. The proof-supported '
     'comparison mean is now 483 with potential range 551; its integer comparison bound remains 235. '
     'Milestone79 supplies encoded guards and ten interval-filter proofs. Full graph interpretation '
     'and potential replay remain. Paper revision76 is unchanged; see [the current handover](handoff/README.md).')
for name in ['README.md','COLLABORATION.md']:
    p=ROOT/name;s=p.read_text();old=next(x for x in s.splitlines() if x.startswith('Latest continuation:'))
    save(p,s.replace(old,new,1))
p=ROOT/'milestones/README.md';s=p.read_text()
entry='- [Milestone 80: 012310 share closure and comparison](80-012310-share-closure/README.md). Case7305 checked; five local targets remain; proof-supported mean483 and range551 still give integer comparison235.\n\n'
if '80-012310-share-closure' not in s:s=s.replace('- [Milestone 79:',entry+'- [Milestone 79:',1)
save(p,s)
p=ROOT/'RESEARCH_LEDGER.md';s=p.read_text();title='## Milestone 80: the 012310 share theorem'
if title not in s:
    s+='\n\n'+title+'\n\n2 November 2026. The selected case7305 refutation completed Lean replay, '
    s+='followed by geometry, reversal and the full source/axiom audit: 465 modules and 100 audits. '
    s+='Every matching six-transition snake window has five-centre scale12 share at least12, '
    s+='without an extra singleton-count hypothesis. Archives restore all465 sources and compact '
    s+='proof bytes. The combined catalogue passes35 audits and retains only cases7301,7302,7303,7307,7308. '
    s+='The exact finite comparison verifies all4947008 edge inequalities and an attaining cycle: '
    s+='mean483, potential range551, bound157625/669 and integer235. Its weights and potential '
    s+='match the formerly assumed012310 comparison. No new global numerical bound follows until '
    s+='the graph/credit/potential assembly is complete. All case7305 proof processes have finished. '
    s+='Paper revision76 is unchanged; the next scheduled rewrite is86.\n'
save(p,s)
p=ROOT/'handoff/CURRENT_STATUS.md';s=p.read_text()
s=s.replace('Milestones 77 through 79 add separate proof interfaces without revising the paper.',
            'Milestones 77 through 80 add proof interfaces and a completed local share theorem without revising the paper.')
old='''Using completed local shares alone gives mean 480 and potential range 536;
its integer comparison still gives 235. Adding the pending 012310 share-12
premise gives mean 483 and range 551, also giving 235. These finite-model
comparisons do not independently replace the contributor's global theorem.'''
new='''Completed local shares, now including the checked 012310 share-12 theorem,
give mean 483 and potential range 551. The exact comparison is 157625/669,
with integer bound235. Its weight and potential hashes match the earlier
comparison that assumed this lemma. The previous completed subset had mean480
and range536. These finite-model calculations do not independently replace
the contributor's global theorem; graph interpretation and Lean potential
replay remain required.'''
assert old in s;s=s.replace(old,new)
s=s.replace('| 012310 | 12 | Replay in progress at recent checkpoints, case7305 |',
            '| 012310 | 12 | Checked, including reversal, case7305 |')
old='''Read the current checkpoint and inspect processes before continuing case7305.
Its 92 semantic/composition checks and partial refutation checks do not establish
its final share theorem. After refutation success, geometry, reversal and the
full source/axiom audit remain necessary.'''
new='''Case7305 completed all465 source modules and100 printed theorem audits,
including geometry and reversal. Its selected sources and compact proof were
archived and restored byte-for-byte. No case7305 proof process remains active.
The combined catalogue passes35 audits and retains exactly five local targets:
7301,7302,7303,7307 and7308. Earlier pending checkpoints remain historical evidence.'''
assert old in s;s=s.replace(old,new)
s=s.replace('the six target share theorems','the five remaining target share theorems')
s=s.replace('single active case7305 completion driver and revalidate its existence before\nany restart.',
            'completed case7305 receipts; inspect actual processes before starting any\nnew case. Do not repeat its successful unchanged replay.')
save(p,s)
p=ROOT/'handoff/README.md';s=p.read_text()
s=s.replace('milestone 79](../milestones/79-retained-edge-guards','milestone 80](../milestones/80-012310-share-closure')
s=s.replace('Its [proof summary](../milestones/79-retained-edge-guards/data/proof-summary.json)\nrecords current Lean checks and exact receipt hashes. Its\n[checkpoint](../milestones/79-retained-edge-guards/data/checkpoint.json)\nrecords repository refs, paper hash and case7305\'s observed process state.',
'''Its [checkpoint](../milestones/80-012310-share-closure/data/checkpoint.json)
records the completed local and combined audits, model comparison, exact
receipt hashes, repository refs and unchanged paper hash.''')
s=s.replace('../milestones/79-retained-edge-guards/data/file-manifest.json','../milestones/80-012310-share-closure/data/file-manifest.json')
s=s.replace('depends on six local shares','depends on five remaining local shares')
start=s.index('Case 7305 replay was active at the checkpoint.')
end=s.index('The [detailed handover]',start)
s=s[:start]+'''Case7305 is complete:465 modules,100 local audits, geometry and reversal.
Its checked archive restores all sources and compact proof bytes. The combined
catalogue passes35 audits with five local targets remaining. No case7305 proof
process was active at the final checkpoint. Earlier pending process snapshots
are historical; do not restart a completed unchanged case.

'''+s[end:]
s=s.replace('hash-matched during milestone79','hash-matched during milestone80')
s=s.replace('A fresh compiler retry failed\nbefore source compilation; its diagnostic is saved in milestone77.',
            'The compiler retry at milestone77 failed\nbefore source compilation; its diagnostic is saved there.')
save(p,s)
p=ROOT/'handoff/NEXT_AGENT_PROMPT.md';s=p.read_text().replace("milestone79's README","milestone80's README")
start=s.index("First inspect case7305's live process")
end=s.index('Milestones 77 and 78',start)
s=s[:start]+'''Case7305 is complete and integrated:465 modules,100 local audits,35 combined
audits. Its theorem gives five-centre scale12 share at least12 for012310 and
the reversed window. Archives and restoration passed. Reuse those results;
do not restart its completed replay. The five remaining local targets are
7301,7302,7303,7307 and7308. The proof-supported finite mean is483 with range551,
giving integer comparison235. Graph interpretation and Lean potential replay
remain necessary before deriving a global bound from this comparison.

'''+s[end:]
s=s.replace('milestones77 through79 have separate','milestones77 through80 have separate')
save(p,s)
p=OLD/'cases/case7305/README.md';s=p.read_text()
start=s.index('This is a preserved partial proof.');end=s.index('`data/pending-checkpoint.json`',start)
s=s[:start]+'''The local theorem is complete as of milestone80. All465 modules and100 printed
theorem audits passed, including the selected refutation, arbitrary-snake
geometry and reversal. `data/proof-audit.json` is the completed audit;
`data/archive.json` pins the exact checked-source and compact-proof archives.
Their restoration verified all465 sources and both proof files. The combined
catalogue now uses this theorem. No case7305 proof process remains active.

The following partial-checkpoint files are retained as historical provenance.
'''+s[end:]
start=s.index("From the repository root, resume the existing case's")
end=s.index('Verify the partial archive',start)
s=s[:start]+'''For reconstruction on a new host, restore the checked archive with the parent
`scripts/restore.py 7305`, then adapt toolchain/support paths and run the case's
`scripts/complete_share.py` followed by `scripts/audit_share.py`. On the current
host, successful unchanged source-matched receipts are reusable. Use one
completion driver per case. The old partial archives remain provenance.

'''+s[end:]
save(p,s)
p=OLD/'README.md';s=p.read_text()
s=s.replace('| 012310 | 12 | 7305 | Pending |','| 012310 | 12 | 7305 | Checked, including reversal |')
s=s.replace('''theorem audits, respectively. The final combined check passes 32 theorem audits
and confirms that the partial catalogue theorem retains exactly the six pending
certificate premises.''','''theorem audits, respectively. Case7305 adds465 modules and100 audits.
The combined check now passes35 theorem audits and retains exactly five pending
certificate premises:7301,7302,7303,7307 and7308.''')
s=s.replace('| Completed cases 7300, 7304, 7306 and the earlier distinct-direction share 12 | 480 | 536 | 10609/45 | 235 |',
            '| Earlier completed subset 7300, 7304, 7306 (historical) | 480 | 536 | 10609/45 | 235 |')
s=s.replace('| The same rules, additionally assuming share 12 for 012310 | 483 | 551 | 157625/669 | 235 |',
            '| Completed cases 7300, 7304, 7305, 7306 and earlier distinct-direction share12 | 483 | 551 | 157625/669 | 235 |')
start=s.index('The completed additions raise 2,351,884 edge weights')
end=s.index('## ',start)
s=s[:start]+'''The completed additions raise2,536,591 edge weights relative to the source
graph. The newly checked012310 lemma removes the former mean480 obstruction;
the exact minimum is now483 with range551. Its weights and potential equal
the earlier comparison that assumed this lemma. The integer comparison remains
235. Current receipt: `data/proved-model.json`; the previous assumed receipt
is retained as historical evidence in `data/assumed-012310x12-model.json`.

'''+s[end:]
s=s.replace('The manuscript remains at revision 66, with the next\nfull rewrite scheduled for milestone 76.',
            'The manuscript remains at revision76, with the next\nfull rewrite scheduled for milestone86.')
save(p,s)
print('Updated current handover and case7305 completion status')
