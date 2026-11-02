"""Record the bounded optimisation result and update the next research target."""
from pathlib import Path
HERE=Path(__file__).resolve().parents[1];ROOT=HERE.parents[1]
save=lambda p,t:p.write_text(t,encoding='utf-8',newline='\n')
latest=('Latest continuation: [milestone 82](milestones/82-unsaturated-cycle-obstruction/README.md) '
    'identifies a four-edge minimum-mean cycle with every stored count below six. Any nonnegative '
    'bonus that vanishes on such edges leaves the mean at 483 and cannot yield 234 under the same '
    'budget, even with zero potential range. Six Lean audits and all 4,947,008 exact edge checks pass. '
    'The pending 012034 and 012340 share targets would raise this witness alone to 497; a full-model '
    'improvement is not inferred. Milestone 81 closes all forty short-rule filters. The maintained '
    'interval stays 191 through 235; see [the current handover](handoff/README.md).')
priority=('Next research priority: test the pending 012034 share-20 and 012340 share-16 targets, '
    'which act directly on the current unsaturated critical cycle. Alternate with completing the '
    'reference union, history exclusions, exact graph membership and credit/potential assembly. '
    'All five pending local share targets remain obligations of the full 234 certificate. '
    'See [the continuation assignment](handoff/NEXT_AGENT_PROMPT.md).')
for name in ['README.md','COLLABORATION.md']:
    path=ROOT/name;lines=path.read_text().splitlines()
    for i,line in enumerate(lines):
        if line.startswith('Latest continuation:'):lines[i]=latest
        if line.startswith('Next research priority:'):lines[i]=priority
    save(path,'\n'.join(lines)+'\n')
path=ROOT/'milestones/README.md';text=path.read_text()
entry=('- [Milestone 82: obstruction from counts below six](82-unsaturated-cycle-obstruction/README.md). '
       'Six Lean audits and exact array checks rule out a class of excess-only bonuses on the current '
       'graph; two pending share targets act on the saved cycle. No global bound changes.\n\n')
if entry not in text:text=text.replace('- [Milestone 81:',entry+'- [Milestone 81:',1)
save(path,text)
path=ROOT/'RESEARCH_LEDGER.md';text=path.read_text();heading='## Milestone 82: unsaturated-cycle obstruction'
if heading not in text:
    text+='\n\n'+heading+'\n\n2 November 2026. '
    text+=('The completed-share graph retains a four-edge cycle of mean 483 whose six-count symbols '
      'are all below six. Every nonnegative bonus vanishing on this class preserves the exact mean; '
      'the old potential remains valid and the same cycle attains it. Six Lean audits check count '
      'literals, cycle telescoping, monotonicity and the strict-budget obstruction. All 4,947,008 '
      'edge inequalities and the exact cycle were independently rechecked against saved array hashes. '
      'At range zero the 234 criterion already lacks 2319 charge units. Cases 7302 and 7307 would '
      'raise this one witness to 497 if their target share bounds are proved; this is not a new '
      'whole-graph mean. The interval remains 191 through 235, all five target local shares and '
      'global assembly obligations remain, and paper revision 76 is unchanged.\n')
save(path,text)
path=ROOT/'handoff/README.md';text=path.read_text()
paragraph=('The latest optimisation checkpoint is [milestone 82](../milestones/82-unsaturated-cycle-obstruction/README.md).\n'
    'Its exact cycle obstruction rules out bonuses confined to stored counts of six on\n'
    'the current graph. The source, six Lean audits, all-edge verification and\n'
    'conditional witness sensitivity are saved with an exact manifest. Cases 7302\n'
    'and 7307 are the next targeted local-share tests; they remain unproved.\n\n')
if paragraph not in text:text=text.replace('The latest proof checkpoint is\n',paragraph+'The latest proof checkpoint is\n',1)
note=("Use its [current saved-file manifest](../milestones/82-unsaturated-cycle-obstruction/data/file-manifest.json)\n"
      "to verify the present checkpoint and shared handover files.\n")
if note not in text:text=text.replace('and 7307 are the next targeted local-share tests; they remain unproved.\n',
    'and 7307 are the next targeted local-share tests; they remain unproved.\n'+note,1)
text=text.replace('supports exact local and staged verification.',
    "records the versions saved with that milestone. Shared handover files have since\n"
    "been updated; use milestone 82's manifest for their current versions.")
save(path,text)
path=ROOT/'handoff/CURRENT_STATUS.md';text=path.read_text()
paragraph=('Milestone 82 supplies another exact obstruction on the completed-share graph.\n'
    'A four-edge cycle of mean 483 has every count symbol below six. Nonnegative\n'
    'bonuses that vanish on such edges preserve this mean. Even range zero cannot\n'
    'meet the current 234 criterion: 227*483 falls short of 111960 by 2319. Six\n'
    'Lean audits check the arithmetic, separately from the exact array checks.\n'
    'This does not establish that the graph cycle occurs in an actual snake.\n\n'
    'On this witness, the pending 012034 floor 20 occurs twice and 012340 floor 16\n'
    'once. Assuming both increases its mean to 497. This concerns one cycle only;\n'
    'the full graph mean and the other pending targets remain unresolved. These\n'
    'two targets are useful next tests within empty-square charging.\n\n')
if paragraph not in text:text=text.replace('## Preservation and environment\n',paragraph+'## Preservation and environment\n',1)
save(path,text)
path=ROOT/'handoff/NEXT_AGENT_PROMPT.md';text=path.read_text()
text=text.replace("and milestone 81's README and exact checkpoint.","and the milestone 81 and 82 READMEs and exact checkpoints.")
paragraph=('For the next optimisation check, prioritize case 7302 (012034, share 20)\n'
    'or case 7307 (012340, share 16), one bounded task at a time. Milestone 82\n'
    'shows why these act on the current four-edge mean-483 cycle. Their proposed\n'
    'floors would raise that witness alone to 497; no full-graph improvement is\n'
    'inferred. Do not spend another round on bonuses that are zero whenever all\n'
    'six stored symbols are below six on the unchanged graph: that entire class\n'
    'leaves its mean at 483 and cannot reach 234 with the current budget.\n\n')
if paragraph not in text:text=text.replace('Avoid repeating the failed monolithic coverage check;',paragraph+'Avoid repeating the failed monolithic coverage check;',1)
text=text.replace('milestones 77 through 81','milestones 77 through 82')
save(path,text)
print('Updated seven current entry points with the bounded obstruction and next targets')
