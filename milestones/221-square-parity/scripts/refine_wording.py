from pathlib import Path
H=Path(__file__).resolve().parents[1];R=H.parents[1]
D=Path('D:/Codex/2026-10-13/new-chat/outputs')
for name,old,new in [
 ('snake9_frontier_explanation.tex','The 93-edge partner needed for 192 remains possible.','The 93-edge partner needed for 192 remains unresolved.'),
 ('snake9_research.tex','generic Lean results, exact finite audits and unresolved numerical\nassembly are distinguished in','generic Lean results, exact finite audits and the remaining Lean\nassembly of the numerical arrays are distinguished in')]:
 p=D/name;s=p.read_text(encoding='utf-8');assert s.count(old)==1
 p.write_text(s.replace(old,new),encoding='utf-8',newline='\n');(R/'paper'/name).write_bytes(p.read_bytes())
print('APPLIED_TWO_REVIEW_REFINEMENTS')
