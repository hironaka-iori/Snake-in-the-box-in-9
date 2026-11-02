"""Refresh current root summaries while preserving older historical entries."""
from pathlib import Path
import subprocess
HERE=Path(__file__).resolve().parents[1];ROOT=HERE.parents[1]
base='1b8ef3193e4b8572f75bfc280768dbd4b02940b6'
active=('Active research: [milestone 73](milestones/73-countfree-share-catalogue/README.md) now supplies '
    'four of the nine target count-free shares: 012031, 012304 and 012314 have floor16; '
    '012310 has floor12. Coverage, canonical coordinate transfer, reversal, global share '
    'accounting and overlap are checked. The combined catalogue retains five local certificate '
    'premises. The full target234 remains conditional on these, graph interpretation and '
    'potential replay. The maintained interval remains **191 <= a(9) <= 235**. '
    'Milestone72 separately retains six unresolved count-certificate cases.')
comparison=('Count-free share continuation: [current comparison](milestones/80-012310-share-closure/README.md) '
    'verifies all4,947,008 edge inequalities and an attaining cycle using checked local shares: '
    'mean483, potential range551 and integer comparison235. Its weights and potential match '
    'the former comparison that assumed the012310 lemma. The full target catalogue still has '
    'mean496, range600 and conditional bound137941/587 < 235. The exact graph-to-snake and '
    'Lean potential assembly remains unfinished.')
replay=('Case7305 is complete:465 modules and100 theorem audits passed, including geometry and '
    'reversal. Its checked archives restore all sources and the compact proof. The completed '
    'catalogue now contains four target cases. No case7305 proof process remains active. '
    'The paper remains revision76 and matches the existing editor source.')
for name in ['README.md','COLLABORATION.md']:
    path=ROOT/name;current=path.read_text()
    latest=next(x for x in current.splitlines() if x.startswith('Latest continuation:'))
    old=subprocess.check_output(['git','-c','core.commitGraph=false','show',base+':'+name],cwd=ROOT).decode('utf-8')
    lines=old.splitlines()
    for i,line in enumerate(lines):
        if line.startswith('Latest continuation:'):lines[i]=latest
        elif line.startswith('Active research:'):lines[i]=active
        elif line.startswith('Count-free share continuation:'):lines[i]=comparison
        elif line.startswith('Case7305 has '):lines[i]=replay
        elif line.startswith('Start with the [updated research handover]'):
            lines[i]='Start with [the current research handover](handoff/README.md). It records the completed case7305 theorem, five remaining local share targets, graph-interpretation gaps and the current comparison. The dated handovers and earlier entries below retain their historical evidence.'
    # Space only the newly introduced current-summary strings.
    text='\n'.join(lines)+'\n'
    for oldword,newword in [('floor16','floor 16'),('floor12','floor 12'),('target234','target 234'),
        ('Milestone72 separately','Milestone 72 separately'),('all4,947,008','all 4,947,008'),
        ('mean483','mean 483'),('range551','range 551'),('comparison235','comparison 235'),
        ('the012310','the 012310'),('mean496','mean 496'),('range600','range 600'),('bound137941','bound 137941'),
        ('Case7305 is complete:465','Case 7305 is complete: 465'),('and100 theorem audits','and 100 theorem audits'),('revision76 and matches','revision 76 and matches')]:
        text=text.replace(oldword,newword)
    path.write_text(text,encoding='utf-8',newline='\n')
path=ROOT/'milestones/README.md';current=path.read_text()
entry=next(x for x in current.splitlines() if x.startswith('- [Milestone 80:'))
old=subprocess.check_output(['git','-c','core.commitGraph=false','show',base+':milestones/README.md'],cwd=ROOT).decode('utf-8')
old=old.replace('Milestone 73 checks three of nine count-free shares','Milestones 73 and 80 check four of nine count-free shares')
old=old.replace('retains six local certificate premises','retains five local certificate premises')
old=old.replace('- [Milestone 79:',entry+'\n\n- [Milestone 79:',1)
path.write_text(old,encoding='utf-8',newline='\n')
for name in ['handoff/CURRENT_STATUS.md','handoff/NEXT_AGENT_PROMPT.md',
             'milestones/73-countfree-share-catalogue/README.md']:
    path=ROOT/name;text=path.read_text().replace('checked012310','checked 012310').replace('now483','now 483').replace('is483','is 483').replace('scale12','scale-12')
    path.write_text(text,encoding='utf-8',newline='\n')
print('Refreshed current root summaries and preserved historical sections')
