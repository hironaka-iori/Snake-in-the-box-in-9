from pathlib import Path
H=Path(__file__).resolve().parents[1];R=H.parents[1]
p=Path('D:/Codex/2026-10-13/new-chat/outputs/snake9_frontier_explanation.tex')
s=p.read_text(encoding='utf-8')
old='Each branch adds its prefix equalities to the model. Exact cardinality\nbounds below 94 exclude branches; every other branch is expanded completely.'
new=r'''Each branch adds its prefix equalities to the model. Each exact
certificate combines inequality rows with nonnegative weights and equality
rows with signed weights, then bounds the remaining coefficients using
$0\le z_j\le1$; numerical optimality is unnecessary. Cardinality bounds
below 94 exclude branches; every other branch is expanded completely.'''
assert s.count(old)==1
p.write_text(s.replace(old,new),encoding='utf-8',newline='\n')
(R/'paper'/p.name).write_bytes(p.read_bytes())
print('EXACT_CERTIFICATE_REASONING_ADDED')
