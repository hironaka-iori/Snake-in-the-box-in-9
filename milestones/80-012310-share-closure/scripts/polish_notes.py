"""Normalize spacing in the current human-readable completion notes."""
from pathlib import Path
import re
HERE=Path(__file__).resolve().parents[1];ROOT=HERE.parents[1]
names=['README.md','COLLABORATION.md','RESEARCH_LEDGER.md','milestones/README.md',
    'handoff/README.md','handoff/CURRENT_STATUS.md','handoff/NEXT_AGENT_PROMPT.md',
    'milestones/73-countfree-share-catalogue/README.md',
    'milestones/73-countfree-share-catalogue/cases/case7305/README.md']
for name in names:
    p=ROOT/name;s=p.read_text()
    # Avoid unrelated historical ledger sections.
    prefix=''
    if name=='RESEARCH_LEDGER.md':
        marker='## Milestone 80:';i=s.index(marker);prefix,s=s[:i],s[i:]
    s=re.sub(r'\b(all|and|passes|adds|least|mean|range|bound|revision|milestone|share|relative to|raise|of|for|including)(?=\d)',r'\1 ',s,flags=re.I)
    s=re.sub(r'(?<=\d),(?=\d{4}(?:,|\.| |$))',', ',s)
    s=re.sub(r'(?<=modules),(?=\d)',', ',s)
    s=re.sub(r'(?<=audits),(?=\d)',', ',s)
    s=s.replace('complete:465','complete: 465').replace('integrated:465','integrated: 465')
    s=s.replace('Case7305','Case 7305').replace('Case 7305 adds465','Case 7305 adds 465')
    s=s.replace('premises:7301','premises: 7301').replace('all4947008','all 4,947,008')
    s=s.replace('mean483','mean 483').replace('integer235','integer 235').replace('comparison235','comparison 235')
    s=s.replace('passes35','passes 35').replace('share12','share 12')
    if name=='handoff/CURRENT_STATUS.md':s=s.replace('of the pending share rules.','of the target share rules.')
    p.write_text(prefix+s,encoding='utf-8',newline='\n')
print('Normalized current completion-note spacing')
