from pathlib import Path
import json,textwrap
H=Path(__file__).resolve().parents[1];R=H.parents[1]
d=json.loads((R/'milestones/121-replacement-window-pressure/data/boundary-paths.json').read_text())
out=[r'\section{Sharp witnesses for the second and fourth counts on $012032$}\label{app:pair-012032-witnesses}',
r'The following complete snakes attain the boundary pairs of Theorem~\ref{thm:pair-012032}. Each transition string starts at the stated integer vertex, which need not be zero. The index $r$ is measured from that initial vertex. The designated segment is $(0,1,3,7,6,14,10)$ in all three cases.']
for x in d['paths']:
 v=x['order'];ts=''.join(str((a^b).bit_length()-1) for a,b in zip(v,v[1:]));assert len(ts)==x['edges']
 out.extend([r'\subsection{The pair $('+','.join(map(str,x['pair']))+')$}',
 f"The snake has {x['edges']} edges, starts at ${v[0]}$, and has the designated window at $r={x['start']}$. Its five internal singleton counts are $("+','.join(map(str,x['counts']))+')$.',r'\begin{quote}\ttfamily\small',
 '\\\\\n'.join(textwrap.wrap(ts,72)),r'\end{quote}'])
out.append(r'Direct reconstruction checks all 30184 unordered vertex pairs across these three snakes, together with the five counts in each designated window. Both endpoints are at Hamming distance two from both counted vertices. Complete Lean checks also verify these paths and counts~\cite{pair012032archive}. The witnesses establish sharpness of the pair inequality; their endpoint geometry alone supplies no universal equality theorem.')
(H/'data/new-witnesses.tex.txt').write_text('\n\n'.join(out)+'\n',encoding='utf-8')
print('Prepared three preserved sharp witnesses.')
