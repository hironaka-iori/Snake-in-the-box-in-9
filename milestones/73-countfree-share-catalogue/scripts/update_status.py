"""Refresh the research summaries from completed audits and model receipts."""
from pathlib import Path
import json
HERE=Path(__file__).resolve().parents[1];ROOT=HERE.parents[1]
read=lambda p:json.loads(p.read_text())
checkpoint=read(HERE/'data/checkpoint.json');integration=read(HERE/'data/integration-audit.json')
model=read(HERE/'data/proved-model.json');candidate=read(HERE/'data/assumed-012310x12-model.json')
done=checkpoint['completed_cases'];assert done==[7300,7304,7306]
assert integration['case_numbers']==done and integration['remaining_local_certificate_cases']==[7301,7302,7303,7305,7307,7308]
assert model['status']=='EXACT_PROOF_SUPPORTED_LOCAL_MODEL'
assert candidate['additional_share_assumptions']==[{'shape':[0,1,2,3,1,0],'share':12}]
active=('Active research: [milestone 73](milestones/73-countfree-share-catalogue/README.md) '
    'checks three of the nine stronger count-free share cases: 012031, 012304 and 012314, each with share at least 16. '
    'The actual-snake shape coverage, canonical coordinate and reversal adapter, global share identity, and five-centre overlap are Lean-checked. '
    'The combined catalogue theorem now retains six explicit local certificate premises. The full target remains conditional 234; '
    'the contributor-checked interval remains **191 <= a(9) <= 235**. Complete graph interpretation and potential replay remain pending. '
    'Milestone 72 separately retains six unresolved count-certificate cases.')
comparison=('Count-free share continuation: [checked and conditional comparisons](milestones/73-countfree-share-catalogue/README.md) '
    f'verify all {model["edges"]:,} edges. Using only completed local shares gives exact mean {model["mean"]} and potential range {model["potential_range"]}. '
    f'Adding the single unproved share-12 premise for 012310 gives mean {candidate["mean"]} and range {candidate["potential_range"]}; '
    f'its integer comparison bound is {candidate["conditional_integer_bound"]}. '
    'The full nine-shape catalogue has mean 496, range 600, and conditional bound 137941/587 < 235. '
    'An exact audit shows every selected share value is necessary for that fixed graph and potential. This does not prove optimality among other proof plans.')
priority=('Next research priority: check case 7305, the count-free share-12 certificate for 012310, then complete the remaining catalogue and graph assembly. '
    'It complements the checked 012345 share-12 and 012314 share-16 rules in a minimal cover of the original critical family. '
    'Reproduction and remaining obligations are in [the continuation record](milestones/73-countfree-share-catalogue/NEXT.md). '
    'The manuscript remains at revision 66, with its next full rewrite scheduled for milestone 76.')
def replace_paragraph(text,start,new):
    begin=text.index(start);end=text.find('\n\n',begin)
    if end<0:end=len(text)
    return text[:begin]+new+text[end:]
for name in ['README.md','COLLABORATION.md']:
    path=ROOT/name;text=path.read_text(encoding='utf-8')
    text=replace_paragraph(text,'Active research:',active)
    if 'Count-free share continuation:' in text:text=replace_paragraph(text,'Count-free share continuation:',comparison)
    else:text=text.replace(active,active+'\n\n'+comparison,1)
    text=replace_paragraph(text,'Next research priority:',priority)
    if name=='COLLABORATION.md':
        text=text.replace('Checkpoint: 30 October 2026.','Checkpoint: 2 November 2026.',1)
        text=text.replace('Current mathematical checkpoint: [milestone 71]','Preceding completed mathematical checkpoint: [milestone 71]',1)
    path.write_text(text,encoding='utf-8',newline='\n')
path=ROOT/'RESEARCH_LEDGER.md';text=path.read_text(encoding='utf-8')
heading='## Milestone 73: count-free catalogue and global accounting, 2 November 2026'
if heading in text:text=text[:text.index(heading)].rstrip()+'\n'
text+='\n\n'+heading+'\n\n'+active+'\n\n'+comparison+'\n\n'+priority+'\n'
path.write_text(text,encoding='utf-8',newline='\n')
path=ROOT/'milestones/README.md';text=path.read_text(encoding='utf-8')
intro=('The exact optimum remains unresolved. The contributor-checked interval is 191 <= a(9) <= 235 edges. '
    'Milestone 73 checks three of nine count-free shares, actual-snake catalogue coverage, canonical dispatch and global share accounting. '
    'The combined catalogue theorem retains six local certificate premises; 234 remains conditional on these and the graph assembly. '
    'The manuscript is at revision 66, with its next full rewrite scheduled for milestone 76.')
text=replace_paragraph(text,'The exact optimum remains unresolved.',intro)
entry='- [Milestone 73: count-free catalogue and global accounting](73-countfree-share-catalogue/README.md)'
if entry not in text:text=text.replace('\n- [Milestone 72:', '\n'+entry+'\n\n- [Milestone 72:',1)
path.write_text(text,encoding='utf-8',newline='\n')
print('Updated README, collaborator handoff, research ledger and milestone index.',flush=True)
