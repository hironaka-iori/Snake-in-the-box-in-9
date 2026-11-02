"""Refresh current entry points without changing historical milestone records."""
from pathlib import Path
import json
HERE=Path(__file__).resolve().parents[1];ROOT=HERE.parents[1]
receipt=json.loads((HERE/'data/proof-summary.json').read_text())
assert receipt['status']=='PASS_DIRECTION_AND_HISTORY_SHAPE_INTERFACES'
n=receipt['printed_theorem_audits']
new=(f'Latest continuation: [milestone 77](milestones/77-direction-state-coverage/README.md) '
    f'adds {n} successful Lean theorem audits for direction coverage, numeric lookup, actual direction states '
    'and history-shape compatibility. The full graph interpretation and conditional target 234 remain '
    'incomplete. The paper remains revision76. Use [the current handover](handoff/README.md) for '
    'mathematical status, saved evidence, live-process precautions and the next research assignment.')
for name in ['README.md','COLLABORATION.md']:
    p=ROOT/name;s=p.read_text();old=next(line for line in s.splitlines() if line.startswith('Latest continuation:'))
    p.write_text(s.replace(old,new,1),encoding='utf-8',newline='\n')
p=ROOT/'milestones/README.md';s=p.read_text();marker='- [Milestone 76:'
entry=(f'- [Milestone 77: actual direction states and history compatibility](77-direction-state-coverage/README.md). '
       f'{n} Lean theorem audits; complete retained-edge interpretation and the target234 remain pending.\n\n')
if '77-direction-state-coverage' not in s:s=s.replace(marker,entry+marker,1)
p.write_text(s,encoding='utf-8',newline='\n')
p=ROOT/'RESEARCH_LEDGER.md';s=p.read_text();title='## Milestone77: direction and history-shape interfaces'
if title not in s:
    s+='\n\n'+title+f'\n\n2 November2026. {n} printed theorem audits passed Lean4.19.0. '
    s+='Every actual eight/nine-direction window has a valid recorded ID, with consecutive source/target '
    s+='states; numeric history decoding, signature equivalence and nonempty-history shape compatibility '
    s+='are checked. Finite coverage and lookup are split into kernel-checked blocks to control memory. '
    s+='The concrete history update, combined count state, exclusions, credits, retained edges and full '
    s+='potential interpretation remain. No numerical bound changed. Case7305 final share theorem remains '
    s+='pending; successful replay rows and actual process observation are frozen in milestone77. '
    s+='Paper revision76 is unchanged and hash-matched; the compiler retry failed before source compilation. '
    s+='The current handover and continuation prompt are in handoff/.\n'
p.write_text(s,encoding='utf-8',newline='\n')
print('Updated current repository entry points')
