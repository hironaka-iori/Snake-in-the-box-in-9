"""Update the existing manuscripts after accepted proof and query receipts."""
from pathlib import Path
import json
H=Path(__file__).resolve().parents[1]; R=H.parents[1]
D=Path('D:/Codex/2026-10-13/new-chat/outputs')
s=json.loads((H/'data/search-summary.json').read_bytes())
assert not (H/'data/partner-search.lock').exists()
for n in ['Cycle218','PartnerParity218']:
    d=json.loads((H/'data'/(n+'-audit.json')).read_bytes()); assert d['status']=='PASS'
for name in ['snake9_research.tex','snake9_frontier_explanation.tex']:
    p=H/'data'/('before-'+name); assert not p.exists(); p.write_bytes((D/name).read_bytes())
main=(D/'snake9_research.tex').read_text(encoding='utf-8')
front=(D/'snake9_frontier_explanation.tex').read_text(encoding='utf-8')
main=main.replace('Research state after round 217, 15 November 2026','Research state after round 218, 15 November 2026',1)
front=front.replace('Research state after round 217','Research state after round 218',1)
body=r'''
\subsection{Preserving compatible paths under cycle exclusions}
\label{sec:partner218}
The direct partner search selects 94 vertices of the allowed graph.
The joining endpoint is selected and has degree one; one other selected
vertex is an endpoint, and every remaining selected vertex has degree two.
These degree equations apply only to selected vertices. No condition
restricts the partner to a copy, prefix or local modification of a saved path.

The joining vertices 0 and 78 have even parity. Each cube edge flips parity,
so the 94 positions of a 93-edge partner contain 47 vertices of each parity,
and the free endpoint has odd parity. The propagation of parity from
actual consecutive path edges, the final endpoint parity and the two
counts are checked in Lean for equal-length Boolean-word paths.

\begin{proposition}\label{prop:cycle-cut218}
Let $C$ be the vertex set of a simple cycle in a symmetric graph, and let
$S$ be contained in the vertex set of an induced path. Then
\[
|S\cap C|\le |C|-1.
\]
The cycle need not be induced.
\end{proposition}
\begin{proof}
If all cycle vertices belonged to the path, choose the one appearing
last along the path. Its two distinct cycle neighbours would both
appear earlier. Inducedness would force both to be its immediately
preceding path vertex, a contradiction. At least one cycle vertex is
therefore missing, which gives the inequality.
\end{proof}
Lean checks both noncontainment and the resulting count, with explicit
cycle distinctness, consecutive edges and the closing edge.

The degree conditions alone permit one path and additional disjoint cycles.
The search initially excludes every saved coordinate square and every
saved six-cycle obtained by removing antipodal vertices from a three-face.
These give 279 initial cuts for endpoint 0 and 274 for endpoint 78.
Whenever a returned selection has a separate cycle, the same inequality
excludes that cycle and the model is solved again. A connected selection
must still pass direct induced-path and joining checks. The generic Lean
results do not certify numerical cycle extraction, constraint serialization
or native solver exhaustion~\cite{research218}.

'''
for row in s['roots']:
    body+=(f'At endpoint {row["root"]}, the 240-second query returns '
           +r'\texttt{'+row['status']+'}, after '
           +f'{row["solver_seconds"]:.3f} reported solver seconds; '
           +f'{row["dynamic_cycle_cuts"]} dynamic cycle cuts are added.\n')
if s['both_native_excluded']:
    body+=('Both endpoint cases are excluded at the native-solver evidence level. '
           'This rules out this fixed-parent 192-edge construction subject to those '
           'computations, without a Lean contradiction certificate or global upper bound.\n\n')
else:
    body+=('The unresolved cases remain open. No longer snake or global numerical '
           'bound is obtained, and no speed comparison is established.\n\n')
body+=('An initial invocation exceeded the memory limit before producing a model '
       'or mathematical result. Limiting the numerical-library thread counts '
       'allowed the same model to run within the recorded resource limits. '
       'The failed invocation and subsequent receipts are retained separately.\n\n')
anchor='\\section{Verification scope and remaining problem}\\label{sec:verification}'
assert main.count(anchor)==1; main=main.replace(anchor,body+anchor,1)
bib=r'''
\bibitem{research218}
Snake-in-the-box project. \emph{Direct compatible-partner queries, parity
and cycle-cut preservation}. Research milestone 218, 15 November 2026.
\url{https://github.com/hironaka-iori/Snake-in-the-box-in-9/tree/main/milestones/218-direct-partner}.

'''
main=main.replace('\\end{thebibliography}',bib+'\\end{thebibliography}',1)
brief=r'''
\paragraph{The partner model and its cycle cuts.}
A 93-edge partner beginning at an even vertex uses 47 vertices of each
parity and ends at an odd vertex. Lean derives these facts from actual
consecutive cube edges. The new model leaves that odd endpoint free
and requires degree one at the two selected endpoints and degree two
at every other selected vertex.

Separate cycles can satisfy these degree conditions. For every cycle
$C$, an induced path must omit at least one vertex of $C$.
Indeed, the last cycle vertex along the path cannot have two distinct
earlier cycle neighbours: both would have to be its immediate predecessor.
Lean checks this argument and the inequality $|S\cap C|\le |C|-1$
for a selection $S$ drawn from an actual induced path. Numerical cycle
extraction and solver exhaustion remain separate verification obligations.

'''
brief+='The two new 240-second endpoint queries return '+', '.join(
    r'\texttt{'+row['status']+'} at '+str(row['root']) for row in s['roots'])+'. '
if s['both_native_excluded']:
    brief+='These exclude the fixed-parent target computationally; a Lean contradiction certificate remains absent. '
else:
    brief+='Every unresolved query remains open. '
brief+='No new global bound or longer snake is obtained.\n\n'
front=front.replace('\\section{What would resolve the question}',brief+'\\section{What would resolve the question}',1)
front=front.replace('milestones through round 217','milestones through round 218',1)
for name,source in [('snake9_research.tex',main),('snake9_frontier_explanation.tex',front)]:
    (D/name).write_text(source,encoding='utf-8',newline='\n')
    (R/'paper'/name).write_bytes((D/name).read_bytes())
print('UPDATED_EXISTING_MANUSCRIPTS')
