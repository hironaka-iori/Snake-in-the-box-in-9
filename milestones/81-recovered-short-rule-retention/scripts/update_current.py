"""Update current entry points; preserve historical milestone records."""
from pathlib import Path
HERE=Path(__file__).resolve().parents[1];ROOT=HERE.parents[1]
def save(path,text):path.write_text(text,encoding='utf-8',newline='\n')
latest=('Latest continuation: [milestone 81](milestones/81-recovered-short-rule-retention/README.md) '
    'proves that all forty recovered short-rule filters preserve eligible windows of every actual snake, '
    'with both orientations and correct count truncation. Eight modules passed 66 Lean theorem audits; '
    'an exact builder comparison covers 23,561,280 direction/count pairs. Existing certificate objects '
    'were reused with hashes. The reference union, three history exclusions, retained-array membership, '
    'credit interpretation and potential replay remain. The project interval remains 191 through 235; '
    '234 is conditional. Paper revision 76 is unchanged. See [the current handover](handoff/README.md).')
priority=('Next research priority: complete the reference union and history-exclusion interpretation, '
    'then exact retained-array membership and credit accounting. Case 7305 is complete; five local '
    'share targets remain. Alternate these proof obligations with bounded tests that could improve '
    'the conditional charge calculation. See [the continuation assignment](handoff/NEXT_AGENT_PROMPT.md).')
for name in ['README.md','COLLABORATION.md']:
    path=ROOT/name;lines=path.read_text().splitlines()
    for i,line in enumerate(lines):
        if line.startswith('Latest continuation:'):lines[i]=latest
        if line.startswith('Next research priority:'):lines[i]=priority
    save(path,'\n'.join(lines)+'\n')
path=ROOT/'milestones/README.md';text=path.read_text()
entry=('- [Milestone 81: forty recovered short-rule filters](81-recovered-short-rule-retention/README.md). '
       '66 Lean audits close this retention family; the exact isolated builder loop agrees on '
       '23,561,280 pairs. Full graph membership and the numerical bounds are unchanged.\n\n')
if entry not in text:text=text.replace('- [Milestone 80:',entry+'- [Milestone 80:',1)
save(path,text)
path=ROOT/'RESEARCH_LEDGER.md';text=path.read_text()
heading='## Milestone 81: retention under forty recovered short rules'
if heading not in text:
    text+='\n\n'+heading+'\n\n2 November 2026. Eight Lean modules passed 66 printed theorem audits. '
    text+=('All forty recovered short filters now preserve actual snake windows at every fitting offset '
      'and in both orientations, with explicit represented-position and count-saturation conditions. '
      'Three small semantic support sources were checked again; 970 certificate objects were reused '
      'with pinned source/object hashes. The exact builder-loop comparison covers 23,561,280 '
      'direction/count pairs and 7,927 placements, with reconstructed and hash-pinned inputs. '
      'Independent review found no outstanding defect within this scope. The reference union, three '
      'history exclusions, retained-array membership, credits and potential replay remain. The '
      'maintained interval stays 191 through 235; 234 retains five local share targets and global '
      'assembly obligations. Paper revision 76 is unchanged, with the next full revision scheduled '
      'for 86. All receipts, exact manifests and continuation instructions are saved locally.\n')
save(path,text)
path=ROOT/'handoff/README.md';text=path.read_text()
text=text.replace('milestone 80','milestone 81').replace('80-012310-share-closure','81-recovered-short-rule-retention')
text=text.replace('records the completed local and combined audits, model comparison, exact',
                  'records the forty-rule retention theorem, 66 audits, exact-loop comparison,')
text=text.replace('and instantiates the ten completed interval filters. The remaining retained-edge\nwork covers the reference union, recovered short rules, history exclusions and',
                  'and instantiates the ten completed interval filters. Milestone 81 closes the forty\nrecovered short filters. The remaining retained-edge work covers the reference\nunion, three history exclusions and')
save(path,text)
path=ROOT/'handoff/CURRENT_STATUS.md';text=path.read_text()
text=text.replace('Milestones 77 through 80 add proof interfaces and a completed local share theorem without revising the paper.',
                  'Milestones 77 through 81 add proof interfaces, a completed local share theorem and\nforty-rule retention without revising the paper. The next full revision is 86.')
old=('The remaining retained-edge work is the 1,378-key reference union, forty\n'
     'recovered short rules, three history exclusions and the exact retained-array\n'
     'index.')
new=('Milestone 81 closes the forty recovered short-rule filters: 66 theorem audits\n'
     'across eight modules, covering both orientations and every fitting represented\n'
     'placement. A separate exact builder-loop comparison checks 23,561,280\n'
     'direction/count pairs, with source reconstruction and complete input hashes.\n'
     'It reuses 970 pinned certificate objects and freshly checks three small support\n'
     'sources. It does not rebuild the entire inherited closure.\n\n'
     'The remaining retained-edge work is the 1,378-key reference union, three\n'
     'history exclusions and the exact retained-array index.')
assert old in text or new in text
text=text.replace(old,new)
text=text.replace('guards, interval-filter assembly, catalogue audit and a later replay observation. Build objects',
                  'guards, interval-filter assembly, catalogue audit and a later replay observation.\nMilestone 81 saves the forty-rule theorem, independent review and exact comparison. Build objects')
save(path,text)
path=ROOT/'handoff/NEXT_AGENT_PROMPT.md';text=path.read_text().replace("milestone 80's README","milestone 81's README")
old=('filters. Reuse these checked interfaces. The next task is to instantiate the\n'
     '1,378-key reference union, the forty recovered short rules and three history\n'
     'exclusions, then supply the exact retained-array index.')
new=('filters. Milestone 81 proves retention under all forty recovered short filters,\n'
     'with 66 audits and an exhaustive isolated-loop comparison. Reuse these checked\n'
     'interfaces. The next assembly task is to instantiate the 1,378-key reference\n'
     'union and three history exclusions, then supply the exact retained-array index.')
assert old in text or new in text
text=text.replace(old,new).replace('milestones77 through80','milestones 77 through 81')
text=text.replace('proof notes. The existing editor file is','proof notes. The next full revision is scheduled for 86. The existing editor file is')
save(path,text)
print('Updated seven current entry points; historical records preserved')
