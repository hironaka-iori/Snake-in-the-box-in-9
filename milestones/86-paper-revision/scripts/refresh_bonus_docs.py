"""Record the extra definition and exact bonus criterion requested during revision."""
from pathlib import Path
import json
HERE=Path(__file__).resolve().parents[1];ROOT=HERE.parents[1]
r=json.loads((HERE/'data/verification.json').read_text());assert r['current_statements']==130 and r['new_lean_checks']==14
def revise_block(s):
    for a,b in [('128 statement','130 statement'),('187 labels','190 labels'),('187 resolved','190 resolved'),
                ('Seven new Lean','Fourteen new Lean'),('seven new Lean','fourteen new Lean'),
                ('seven new logic','fourteen new logic'),('seven new','fourteen new'),
                ('five new propositions','six new propositions and one definition'),('five propositions','six propositions and one definition')]:
        s=s.replace(a,b)
    return s
for name in ['README.md','COLLABORATION.md']:
    p=ROOT/name;s=p.read_text()
    for start in ['Latest continuation:','Current manuscript revision:']:
        a=s.index(start);b=s.index('\n\n',a);block=revise_block(s[a:b])
        if start=='Current manuscript revision:':
            block+=' The zero-bonus subgraph gives an exact criterion for when nonnegative bonuses raise the finite minimum cycle mean.'
        s=s[:a]+block+s[b:]
    p.write_text(s,encoding='utf-8')
p=ROOT/'handoff/CURRENT_STATUS.md';s=p.read_text();a=s.index('The current paper is revision');b=s.index('## Chosen route:',a)
block=revise_block(s[a:b]).replace('8e9ee179a080ff5049ff6731bac6d5676b0c670762e4a07270852492258857ef',r['paper_sha256'])
block=block.replace('comparison arithmetic.','comparison arithmetic. The zero-bonus subgraph supplies an exact\ncriterion for strict improvement of a finite minimum cycle mean.')
s=s[:a]+block+s[b:];p.write_text(s,encoding='utf-8')
p=ROOT/'handoff/NEXT_AGENT_PROMPT.md';s=p.read_text();a=s.index('hyperlink settings. Revision');b=s.index('The existing editor file is',a)
s=s[:a]+revise_block(s[a:b])+s[b:];p.write_text(s,encoding='utf-8')
p=ROOT/'handoff/README.md';s=p.read_text();a=s.index('The latest manuscript');b=s.index('The current proof checkpoint',a)
s=s[:a]+revise_block(s[a:b])+s[b:];p.write_text(s,encoding='utf-8')
p=ROOT/'milestones/README.md';s=p.read_text();a=s.index('- [Milestone 86:');b=s.index('\n\n',a)
s=s[:a]+revise_block(s[a:b])+s[b:];p.write_text(s,encoding='utf-8')
p=ROOT/'RESEARCH_LEDGER.md';s=p.read_text();a=s.index('## Milestone 86:');block=revise_block(s[a:])
block=block.replace('All187 labels','All190 labels')
block+='''
The user's subsequent request encouraged explicit definitions. The revision adds the zero-bonus subgraph and the exact critical-cycle criterion: for a fixed finite graph and nonnegative edge bonuses, the minimum mean increases precisely when every old critical cycle receives positive total bonus. Seven additional Lean checks establish finite attainment, monotonicity, equality/strictness equivalences and the required nonnegative-sum facts, bringing the total to14. This criterion explains the saturation obstruction and does not itself establish234 or the validity of new local shares.
'''
s=s[:a]+block;p.write_text(s,encoding='utf-8')
print('Updated current documents for130 statements,190 labels and14 new Lean checks')
