"""Update the existing editor originals and repository mirrors."""
from pathlib import Path
import json
H=Path(__file__).resolve().parents[1];R=H.parents[1];D=Path('D:/Codex/2026-10-13/new-chat/outputs')
s=json.loads((H/'data/search-summary.json').read_bytes());assert s['complete_through']==42 and s['first_unresolved']==43
n=len(s['widths'][-1]['unresolved'])
for module in ['Simultaneous225','EndpointParity225','IntervalEnlargement225']:
    assert json.loads((H/'data'/(module+'-audit.json')).read_bytes())['status']=='PASS'
table='\n'.join(f"{r['width']}&{r['contexts']}&{r['initial_statuses'].get('INHERITED_EXCLUDED',0)}&{r['initial_statuses'].get('STATIC_EXCLUDED',0)}&{r['initial_statuses'].get('INFEASIBLE',0)+len(r['split_excluded'])}&{len(r['unresolved'])}\\\\" for r in s['widths'])
section=r'''\subsection{Constructing two replacements and transferring exclusions}
\label{sec:replacement225}
\begin{proposition}[Simultaneous replacement criterion]
\label{prop:simultaneous225}
Let $P=(p_0,\ldots,p_n)$ be an induced path and let
$0\le a\le b\le c\le d\le n$. Let $q_0,\ldots,q_n$ agree with $P$
outside $(a,b)\cup(c,d)$. Suppose the sequences on $[a,b]$ and $[c,d]$
are induced paths. Suppose each new interior is disjoint and nonadjacent
to every retained vertex outside its own closed interval, and the two
new interiors are disjoint and nonadjacent. Then $(q_0,\ldots,q_n)$ is
an induced path.
\end{proposition}
\begin{proof}
A pair within one closed replacement interval has the required relation
from its local path. A pair of retained vertices has its relation from
$P$. Every remaining pair joins two new interiors, or a new interior
to a retained vertex outside its closed interval. Separation excludes
equality and adjacency. These indices cannot be consecutive because
the anchors are retained. This proves distinctness and precisely
consecutive adjacency, including shared anchors and empty interiors.
Neither intermediate replacement needs to be valid on its own.
\end{proof}

Enlarging both replacement intervals leaves the same candidate agreeing
with $P$ outside them: the extra positions keep their original vertices.
Thus an excluded containing context excludes the smaller context with
the same complete-path conditions. Only excluded width-44 contexts are
used; an unresolved outcome supplies no exclusion. The constructor and
outside-agreement implication have passed Lean. Numerical exclusions
still depend on the saved native calculations.

For a replacement with endpoints $u,v$, the number $r$ of crossings of
coordinate $h$ satisfies $r=\varepsilon+2k$ for an integer $k\ge0$,
where $\varepsilon=0$ for equal endpoint bits and $\varepsilon=1$
otherwise. Each crossing flips that bit, proving the relation; this
argument has also passed Lean. Crossing allocation remains variable
subject to these parities and the combined total.

For $34\le w\le43$, the $7(w-1)$ maximal contexts are
\[
[a,a+w],\ [c,c+w],\qquad0\le a\le6,\quad144-w\le c\le142.
\]
They cover all pairs of blocks of at most $w$ edges containing positions
7 and 143 in their interiors. The seed, outside indices, anchors,
endpoint 24 and four-crossing target remain fixed. The results are
\begin{center}
\begin{tabular}{rrrrrr}
\toprule
$w$&Contexts&Inherited&Geometric&New solver exclusions&Unresolved\\
\midrule
__TABLE__
\bottomrule
\end{tabular}
\end{center}
At width 42, seven initial timeouts have first interval $[1,43]$ and
second interval $[c,c+42]$, $124\le c\le130$. Both anchor pairs have
equal coordinate bits and the total replacement crossing count is two.
The only allocations are therefore $(0,2)$ and $(2,0)$. All fourteen
allocation queries are infeasible, closing these seven contexts.
The restricted exclusion reaches width 42; width 43 leaves __OPEN__
contexts unresolved after the initial search. Timeout establishes
neither existence nor impossibility. Direct enumeration of connected
replacement paths is the next construction step. A direct search in one width-43 context processed 15,013 complete
first paths in 30 seconds; each left insufficient connected capacity
for the second. A further 30-second search pruned 249,163 partial
branches using that necessary condition. Both searches remain incomplete
and retain their frontiers. These restrictions give no longer snake or global upper bound~\cite{research225}.

'''.replace('__TABLE__',table).replace('__OPEN__',str(n))
short=r'''\subsection{The replacement frontier after round 225}
Two local replacement paths construct a full snake when each is induced,
each new interior is disjoint and nonadjacent to retained vertices
outside its own closed interval, and the
two new interiors are disjoint and nonadjacent. Every pair of vertices
then lies in one local path, is retained, or is separated by one of these
conditions. This proves distinctness and exactly consecutive adjacency.
The direct constructor has passed Lean.

Enlarging a replacement interval keeps the same complete candidate:
the extra positions retain their original vertices. An excluded
containing context therefore excludes the smaller one with the same
target. The outside-agreement implication has passed Lean; numerical
exclusions still rely on the saved native calculations.

The restricted exclusion now reaches two blocks of at most 42 edges.
Of its 287 maximal contexts, 211 inherit exclusions, 69 are excluded by
the initial solver queries and seven require a split. In those seven,
each anchor pair has equal coordinate bits, so each replacement crosses
that coordinate an even number of times. Their total is two, leaving
only $(0,2)$ and $(2,0)$. Both allocations are infeasible in all seven
cases. The parity relation follows because each crossing flips the bit;
it has passed Lean.

Width 43 has 294 contexts, of which __OPEN__ remain unresolved after
the initial search. These finite exclusions concern the selected seed,
unchanged outside indices, endpoint 24 and four crossings. Their solver
contradictions have no Lean certificates and do not prove global
optimality. The construction search now considers actual connected
path pairs in the unresolved contexts~\cite{research225}.

'''.replace('__OPEN__',str(n))
bib=r'''\bibitem{research225}
I.~Hironaka, T.~Ma, and S.~Zhan. \emph{Simultaneous replacement criteria,
containment transfer and crossing-parity search}. Research milestone 225,
15 November 2026.
\url{https://github.com/hironaka-iori/Snake-in-the-box-in-9/tree/main/milestones/225-replacement-widths}.

'''
for name in ['snake9_research.tex','snake9_frontier_explanation.tex']:
    p=D/name;before=(H/'data'/(name+'.before.txt')).read_bytes();assert p.read_bytes()==before
    text=before.decode('utf-8').replace('Research state after round 224','Research state after round 225')
    if name=='snake9_research.tex':
        anchor=r'\section{Verification scope and remaining problem}\label{sec:verification}'
        assert text.count(anchor)==1;text=text.replace(anchor,section+anchor,1)
        old='two-block search through length 33 is excluded natively; longer blocks\nretain unresolved cases.'
        assert old in text;text=text.replace(old,'two-block search through length 42 is excluded natively; width 43\nretains unresolved cases. The direct simultaneous-replacement constructor\nand coordinate-crossing parity relation have also passed Lean.',1)
        old='coverage recorded separately from unresolved cases.'
        text=text.replace(old,old+'\nSection~\\ref{sec:replacement225} adds the checked direct constructor,\ninterval enlargement and endpoint parity. Its width-42 exclusion remains\na native calculation, including the complete two-allocation split.',1)
    else:
        text=text.replace('Research state after round 224','Research state after round 225').replace('milestones through round 224','milestones through round 225')
        anchor=r'\section{Remaining questions}';assert text.count(anchor)==1;text=text.replace(anchor,short+anchor,1)
    assert text.count(r'\end{thebibliography}')==1;text=text.replace(r'\end{thebibliography}',bib+r'\end{thebibliography}',1)
    p.write_bytes(text.encode('utf-8'));(R/'paper'/name).write_bytes(p.read_bytes())
print('UPDATED_EDITOR_ORIGINALS_AND_MIRRORS')
