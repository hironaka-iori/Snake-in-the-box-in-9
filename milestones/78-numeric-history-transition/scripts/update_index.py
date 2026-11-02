"""Update current repository entry points after successful proof verification."""
from pathlib import Path
import json
HERE=Path(__file__).resolve().parents[1];ROOT=HERE.parents[1]
r=json.loads((HERE/'data/proof-summary.json').read_text())
assert r['status']=='PASS_NUMERIC_HISTORY_AND_ENCODED_STATE_SEQUENCE'
new=('Latest continuation: [milestone 78](milestones/78-numeric-history-transition/README.md) '
     'checks the numeric history update and the actual combined state sequence, with 29 Lean theorem audits. '
     'The exact Python selector also agrees on all 37,875 input pairs. Retained-edge membership, credit '
     'interpretation, six local share targets and full potential replay remain before claiming 234. '
     'The paper remains revision 76. Use [the current handover](handoff/README.md) for evidence and continuation.')
for name in ['README.md','COLLABORATION.md']:
    p=ROOT/name;s=p.read_text();old=next(line for line in s.splitlines() if line.startswith('Latest continuation:'))
    p.write_text(s.replace(old,new,1),encoding='utf-8',newline='\n')
p=ROOT/'milestones/README.md';s=p.read_text()
entry='- [Milestone 78: numeric history transitions and actual state sequence](78-numeric-history-transition/README.md). 29 Lean audits; retained-edge membership and charge interpretation remain.\n\n'
if '78-numeric-history-transition' not in s:s=s.replace('- [Milestone 77:',entry+'- [Milestone 77:',1)
p.write_text(s,encoding='utf-8',newline='\n')
p=ROOT/'RESEARCH_LEDGER.md';s=p.read_text();title='## Milestone 78: numeric history transitions and actual state sequence'
if title not in s:
    s+='\n\n'+title+'\n\n2 November 2026. Four modules passed 29 Lean theorem audits. '
    s+='The strict maximum-suffix scan agrees with actual history updates; ties and empty fallback are covered. '
    s+='A rechecked count identity supplies positivity for the actual core counts. The combined direction, '
    s+='history and five-count states have correct numeric endpoints and both history compatibility filters. '
    s+='An executable comparison of the exact builder selector covers all 37,875 pairs. The retained-edge '
    s+='and charge interpretation remains, as do six local share targets and complete potential replay. '
    s+='No numerical bound changes; the case7305 refutation continues under its existing driver. '
    s+='Paper revision76 remains unchanged. Evidence and the precise next task are saved in milestone78 and handoff/.\n'
p.write_text(s,encoding='utf-8',newline='\n')
print('Updated milestone78 entry points')
