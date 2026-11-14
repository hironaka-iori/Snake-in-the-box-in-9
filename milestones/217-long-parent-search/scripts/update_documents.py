"""Update the existing manuscripts after the continuation is terminal."""
from pathlib import Path
import json

H = Path(__file__).resolve().parents[1]
R = H.parents[1]
D = Path('D:/Codex/2026-10-13/new-chat/outputs')
s = json.loads((H / 'data/search-summary.json').read_bytes())
assert s['status'] == 'OPEN', 'Review a witness or completed exclusion separately.'
assert not (H / 'data/history-search.lock').exists()
for name in ['snake9_research.tex', 'snake9_frontier_explanation.tex']:
    p = H / 'data' / ('before-' + name)
    assert not p.exists()
    p.write_bytes((D / name).read_bytes())
main = (D / 'snake9_research.tex').read_text(encoding='utf-8')
front = (D / 'snake9_frontier_explanation.tex').read_text(encoding='utf-8')
main = main.replace('Research state after round 216, 15 November 2026',
                    'Research state after round 217, 15 November 2026', 1)
front = front.replace('Research state after round 216', 'Research state after round 217', 1)
main = main.replace('The case remains open with 9 unfinished regions;',
                    'At the round-216 cutoff, the case remains open with nine unfinished regions;', 1)
front = front.replace('The model remains open with 9 unfinished regions.',
                      'At the round-216 cutoff, the model remains open with nine unfinished regions.', 1)
text = r'''
\subsection{A direct compatible-path target}
\label{sec:direct217}
Longer submitted jobs continue the same retained-coordinate model and
the same joint-support engine. The nine inherited regions and all model
files are unchanged at transfer; the new ledger links the cumulative
predecessor totals explicitly. No additional propagation rule is introduced.
'''
text += (f'The continuation accepts {s["new_jobs"]} jobs and examines '
         f'{s["local_nodes"]:,} additional nodes. The case remains open with '
         f'{s["pending"]} unfinished regions. No different parent or complete '
         'coordinate-case exclusion is obtained. Longer job limits alone '
         'do not establish a speed improvement.\n\n')
text += r'''
The earlier layer records leave a more direct target for improving the
lower bound. Fix the saved 98-edge path $P\subset Q_8$ and one of its
endpoints $t\in\{0,78\}$. Search for a 93-edge induced path starting at
$t$ in
\[
Q_8\bigl[V(Q_8)\setminus(V(P)\setminus\{t\})\bigr].
\]
Its other endpoint is unrestricted. The two paths then have exactly one
common projected vertex, which is an endpoint of each. Placing them in
opposite faces and joining at that vertex gives $98+93+1=192$ edges:
cross-face cube edges occur only between equal projected vertices.
The general joining implication was already checked in Lean.

For this fixed parent, the earlier arbitrary 97-edge partner queries
returned infeasible at both endpoints. These are solver exclusions
without Lean contradiction certificates. In contrast, the 93-edge
queries both remained unresolved after approximately 30 seconds.
Thus finding a different optimal parent is an additional discovery
stage that is unnecessary for the still-open 192-edge target.
Neither outcome settles the conjectured value 196.

Both allowed graphs have 158 vertices, 337 edges and 79 vertices of
each parity. The saved enumeration finds that each graph is connected
and has no articulation vertex. These facts give no elementary
connectivity or parity obstruction to a 93-edge partner. The next
search will consider all such partners, using selected-vertex degree
conditions and cycle exclusions as an alternative to the earlier
circuit formulation. Its runtime advantage is unproved.
The source review, graph data and continuation records are retained
in milestone 217~\cite{research217}.

'''
anchor = '\\section{Verification scope and remaining problem}\\label{sec:verification}'
assert main.count(anchor) == 1
main = main.replace(anchor, text + anchor, 1)
bib = r'''
\bibitem{research217}
Snake-in-the-box project. \emph{Longer parent-search jobs and the direct
93-edge compatible-path target}. Research milestone 217, 15 November 2026.
\url{https://github.com/hironaka-iori/Snake-in-the-box-in-9/tree/main/milestones/217-long-parent-search}.

'''
main = main.replace('\\end{thebibliography}', bib + '\\end{thebibliography}', 1)
brief = r'''
\paragraph{A direct target for 192 edges.}
The saved 98-edge $Q_8$ path can still be used directly. At either
endpoint $t$, remove its other 98 vertices and seek a 93-edge induced
path starting at $t$, with its other endpoint free. The paths share
only $t$, so their copies in opposite faces join to give
$98+93+1=192$ edges. The reason is that a cross-face cube edge requires
equal projected vertices. This is an application of the previously
checked joining theorem.

The old 93-edge queries at both endpoints remain unresolved. The
97-edge queries for the same parent have solver exclusions, without
Lean contradiction certificates. The 192-edge target therefore does
not require a new optimal parent. Each allowed graph has 158 vertices,
337 edges and equal parity classes of size 79; neither has an
articulation vertex. The next direct search will use degree conditions
and cycle exclusions, with no assumed speed improvement.

'''
brief += (f'The longer continuation of the different-parent search examines '
          f'{s["local_nodes"]:,} additional nodes. It remains open with '
          f'{s["pending"]} unfinished regions and produces no new parent.\n\n')
front = front.replace('\\section{What would resolve the question}',
                      brief + '\\section{What would resolve the question}', 1)
old = ('The construction route needs a genuinely different compatible parent\n'
       'or face arrangement and a checked joining construction. Finding a new\n'
       '$Q_8$ parent alone would not prove a longer $Q_9$ snake.')
new = ('A compatible 93-edge partner for the saved parent would improve the\n'
       'lower bound to 192. Other constructions may use a different parent\n'
       'or face arrangement. Finding a new $Q_8$ parent alone would still\n'
       'require a compatible joining construction.')
assert old in front
front = front.replace(old, new, 1)
front = front.replace('milestones through round 216', 'milestones through round 217', 1)
for name, source in [('snake9_research.tex', main), ('snake9_frontier_explanation.tex', front)]:
    (D / name).write_text(source, encoding='utf-8', newline='\n')
    (R / 'paper' / name).write_bytes((D / name).read_bytes())
print('UPDATED_EXISTING_MANUSCRIPTS')
