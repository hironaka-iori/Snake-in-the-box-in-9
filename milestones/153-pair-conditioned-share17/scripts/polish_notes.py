"""Normalize spacing only in this milestone's new prose and handoff prefixes."""
from pathlib import Path
import re
H=Path(__file__).resolve().parents[1];R=H.parents[1]
def polish(s):
    # Keep paths, identifiers and displayed mathematical lines unchanged.
    lines=[]
    for line in s.splitlines(keepends=True):
        if '/' in line or '`' in line or '\\' in line:
            lines.append(line);continue
        line=re.sub(r'(?<=[A-Za-z])(?=\d)|(?<=\d)(?=[A-Za-z])',' ',line)
        line=re.sub(r'(?<=[A-Za-z])(?=\()',' ',line)
        line=re.sub(r'(?<=\d)and(?=\d)',' and ',line)
        lines.append(line)
    return ''.join(lines)
for p in [H/'README.md',H/'MATHEMATICAL_NOTE.md']:
    p.write_text(polish(p.read_text(encoding='utf-8')),encoding='utf-8',newline='\n')
for name in ['README.md','COLLABORATION.md','RESEARCH_LEDGER.md','WORKSPACE.md','milestones/README.md','handoff/README.md','handoff/CURRENT_STATUS.md']:
    p=R/name;s=p.read_text(encoding='utf-8-sig');head,marker,tail=s.partition('# Research update: milestone 152')
    assert marker and head.startswith('# Research update: milestone 153')
    p.write_text(polish(head)+marker+tail,encoding='utf-8',newline='\n')
p=R/'handoff/NEXT_AGENT_PROMPT.md';s=p.read_text(encoding='utf-8-sig');head,marker,tail=s.partition('# Continue after the milestone 152 running checkpoint')
assert marker and head.startswith('# Continue after milestone 153')
p.write_text(polish(head)+marker+tail,encoding='utf-8',newline='\n')
print('POLISHED_NEW153_PROSE_ONLY')
