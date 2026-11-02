"""Update current entry points only after the complete milestone79 check passes."""
from pathlib import Path
import json
HERE=Path(__file__).resolve().parents[1];ROOT=HERE.parents[1]
r=json.loads((HERE/'data/proof-summary.json').read_text())
assert r['status']=='PASS_ENCODED_GUARDS_AND_TEN_INTERVAL_RETENTION'
new=('Latest continuation: [milestone 79](milestones/79-retained-edge-guards/README.md) '
     'checks encoded count slices, reversal and saturation, and proves that every actual snake survives '
     'the ten completed interval filters, with 31 Lean theorem audits. The full reference catalogue, '
     'recovered short rules, history exclusions, credit interpretation, six local share targets and '
     'potential replay remain before claiming 234. Paper revision 76 is unchanged. '
     'Use [the current handover](handoff/README.md) for evidence and continuation.')
for name in ['README.md','COLLABORATION.md']:
    p=ROOT/name;s=p.read_text();old=next(line for line in s.splitlines() if line.startswith('Latest continuation:'))
    p.write_text(s.replace(old,new,1),encoding='utf-8',newline='\n')
p=ROOT/'milestones/README.md';s=p.read_text()
entry='- [Milestone 79: encoded guards and ten interval exclusions](79-retained-edge-guards/README.md). 31 Lean audits; actual snakes survive the ten completed interval filters. Full graph membership remains.\n\n'
if '79-retained-edge-guards' not in s:s=s.replace('- [Milestone 78:',entry+'- [Milestone 78:',1)
p.write_text(s,encoding='utf-8',newline='\n')
p=ROOT/'RESEARCH_LEDGER.md';s=p.read_text();title='## Milestone 79: encoded guards and ten interval exclusions'
if title not in s:
    s+='\n\n'+title+'\n\n2 November 2026. Six modules passed 31 Lean theorem audits. '
    s+='Base-six slices and digits agree with actual singleton counts; encoding injectivity, '
    s+='coordinate normalization, reversal and interval saturation are checked. The ten completed '
    s+='milestone72 interval refutations now imply retention under their encoded graph filters, '
    s+='at all three offsets and in both orientations. Existing certificate objects were reused '
    s+='with source/object hashes, without a clean rebuild of their entire dependency closure. '
    s+='The 1378-key reference union has inspected contributor proofs but is not instantiated '
    s+='in this environment. Recovered short rules, history exclusions, array membership, credits '
    s+='and potential remain. The finite audit covered 2799360 interval-guard comparisons. '
    s+='No numerical bound changed. Case7305 remains pending until its final local audit passes; '
    s+='the exact observed process and successful modules are saved in the checkpoint. '
    s+='Paper revision76 is unchanged.\n'
p.write_text(s,encoding='utf-8',newline='\n')
p=ROOT/'handoff/CURRENT_STATUS.md';s=p.read_text()
s=s.replace('Milestones 77 and 78 add separate proof interfaces without revising the paper.',
            'Milestones 77 through 79 add separate proof interfaces without revising the paper.')
old="The next bounded task is retained-edge membership: prove that every actual\ndirection/history/six-count triple survives the current model's reference,\nrecovered-rule, interval and history exclusions, then identify its retained\narray index. Each exclusion needs its geometric theorem."
new='''Milestone79 adds 31 theorem audits. Its count-slice, digit, encoding-injectivity,
reversal and saturation results connect encoded graph tests to actual counts.
Every actual snake survives the ten completed milestone72 interval filters,
at all three offsets and in both orientations. The closed local certificates
are imported from pinned existing objects, without a clean dependency rebuild.

The remaining retained-edge work is the 1,378-key reference union, forty
recovered short rules, three history exclusions and the exact retained-array
index. The reference theorem sources and contributor logs were audited; their
complete union is still uninstantiated in the current environment.'''
assert old in s;s=s.replace(old,new)
s=s.replace('Milestone 78 saves the current selector/state checks and\na later read-only replay observation.',
            'Milestone 78 saves the selector/state checks. Milestone79 saves the encoded\nguards, interval-filter assembly, catalogue audit and a later replay observation.')
p.write_text(s,encoding='utf-8',newline='\n')
p=ROOT/'handoff/README.md';s=p.read_text()
s=s.replace('milestone 78','milestone 79').replace('78-numeric-history-transition','79-retained-edge-guards').replace('41012','72392')
s=s.replace('Milestones 77 and 78 connect actual snake windows to one consistent numeric\nstate sequence, including histories and counts. The next graph step is\nretained-edge membership, followed by credit interpretation.',
'''Milestones 77 and 78 connect actual snake windows to one consistent numeric
state sequence. Milestone79 connects encoded counts to exclusion predicates
and instantiates the ten completed interval filters. The remaining retained-edge
work covers the reference union, recovered short rules, history exclusions and
the exact array index; credit interpretation follows.''')
s=s.replace('hash-matched during milestone78','hash-matched during milestone79')
p.write_text(s,encoding='utf-8',newline='\n')
p=ROOT/'handoff/NEXT_AGENT_PROMPT.md';s=p.read_text().replace("milestone78's README","milestone79's README")
old='''The next task is to prove that each actual direction/history/six-count triple
survives the exact graph's exclusions, then supply its retained array index.
Check the reference, recovered-rule, history and any later interval guards
against their geometric theorems.'''
new='''Milestone79 checks encoded count slices/digits, injectivity, reversal and
saturation, and proves retention under all ten completed milestone72 interval
filters. Reuse these checked interfaces. The next task is to instantiate the
1,378-key reference union, the forty recovered short rules and three history
exclusions, then supply the exact retained-array index. The current reference
interfaces still have explicit Refuted premises. The closed reference proofs
are in pinned contributor revisions and saved audits, with the current local
snapshot under milestone51. Their full union is not yet imported here.'''
assert old in s;s=s.replace(old,new)
s=s.replace('milestones77 and78 have separate\nproof notes','milestones77 through79 have separate\nproof notes')
p.write_text(s,encoding='utf-8',newline='\n')
print('Updated milestone79 entry points')
