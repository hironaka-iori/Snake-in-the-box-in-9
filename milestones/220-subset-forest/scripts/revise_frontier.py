from pathlib import Path
import re,json
H=Path(__file__).resolve().parents[1];R=H.parents[1]
p=Path('D:/Codex/2026-10-13/new-chat/outputs/snake9_frontier_explanation.tex')
old=(H/'data/before-snake9_frontier_explanation.tex').read_text(encoding='utf-8');assert p.read_text(encoding='utf-8')==old
body=(H/'scripts/frontier_body.txt').read_text(encoding='utf-8')
a='Both exceed 94. Exact potentials certify every simple-cycle occupancy\ninequality, and 158 feasible flows per root certify every subset inequality\nthrough its boundary form.'
b=r'''Both exceed 94. To check all cycle inequalities, put $w_u=1-x_u$.
For each deleted edge $ab$, a rational potential has $p_a=0$,
$|p_u-p_v|\le w_u+w_v$ on other edges, and $p_b+w_a+w_b\ge2$.
Summing along the rest of any cycle gives $2\sum_{u\in C}w_u\ge2$,
which is the required occupancy bound. Separately, 158 feasible flows
per root certify every subset inequality: a flow of at least $2x_v$
from $v$ to an added sink is bounded by every cut separating them.
The cut capacity is exactly $B+E$.'''
assert body.count(a)==1;body=body.replace(a,b)
head=old[:old.index(r'\section{Question and evidence}')].replace('Research state after round 219','Research state after round 220')
tail=old[old.index(r'\begin{thebibliography}'):]
tail=tail.replace(r'\begin{thebibliography}{1}',r'\begin{thebibliography}{9}')
tail=tail.replace(r'\end{thebibliography}',(H/'scripts/new_bibliography.txt').read_text(encoding='utf-8')+r'\end{thebibliography}')
new=head+body+'\n'+tail
assert re.search(r'\\author\{[^\n]*',old).group()==re.search(r'\\author\{[^\n]*',new).group()
p.write_text(new,encoding='utf-8',newline='\n');(R/'paper'/p.name).write_bytes(p.read_bytes())
(H/'data/frontier-edit-record.json').write_text(json.dumps({'old_lines':len(old.splitlines()),'new_lines':len(new.splitlines()),'authors_preserved':True,'scope':'Full explanatory body consolidated; current deduction chain and proof limitations retained.'},indent=2)+'\n')
print('REVISED_FRONTIER',len(new.splitlines()),'LINES')
