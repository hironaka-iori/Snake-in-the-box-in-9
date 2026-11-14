from pathlib import Path
import json
H=Path(__file__).resolve().parents[1];R=H.parents[1]
D=Path('D:/Codex/2026-10-13/new-chat/outputs')
assert json.loads((H/'data/PathSupport213-audit.json').read_bytes())['status']=='PASS'
changes={
'snake9_research.tex':('partner completeness for both parity families~\\cite{research213}.','partner completeness for both parity families~\\cite{research213}.\nA further checked composition supplies support-filter preservation\ndirectly from this reconstructed-path premise: two forced even\nexceptions or six forced odd exceptions exhaust the allowance in a\n32-word pool. Domain containment and assignment fitting remain explicit.'),
'snake9_frontier_explanation.tex':('connected to the actual reconstructed path. Alphabet membership,','connected to the actual reconstructed path. A checked composition\nalso justifies support filtering when two even or six odd exceptions\nexhaust the allowance in a 32-word pool. Alphabet membership,')}
for name,(old,new) in changes.items():
    p=D/name;s=p.read_text(encoding='utf-8');assert s.count(old)==1;s=s.replace(old,new,1)
    p.write_text(s,encoding='utf-8',newline='\n');(R/'paper'/name).write_bytes(p.read_bytes())
print('RECORDED_PATH_SUPPORT_COMPOSITION')
