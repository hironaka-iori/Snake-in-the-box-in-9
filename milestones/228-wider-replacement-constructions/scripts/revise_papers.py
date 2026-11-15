"""Update the existing papers with the bounded width-45 construction result."""
from pathlib import Path
import json
H=Path(__file__).resolve().parents[1];R=H.parents[1];D=Path('D:/Codex/2026-10-13/new-chat/outputs')
assert json.loads((H/'data/coverage45.json').read_bytes())['status']=='COMPLETE_NATIVE_EXCLUSION'
assert json.loads((H/'data/AllocationFacts228-audit.json').read_bytes())['status']=='PASS'
section=r'''\subsection{Two lower paths when both replacements cross the face}
\label{sec:width45}
The same reduction applies when both replacement paths cross the chosen
coordinate. For the fixed seed and endpoint 24, the maximal width-45
intervals are $[a,a+45]$, $0\le a\le6$, and $[c,c+45]$,
$99\le c\le142$. There are $7\cdot44=308$ contexts. Each replacement
has 46 vertices, retains its original anchors, and must avoid every
retained outside vertex except at the intended consecutive joins.

\begin{proposition}[Prescribed upper portions for two replacements]
\label{prop:twofixedupper228}
In $Q_n=Q_{n-1}\times\{0,1\}$, suppose each of two replacement paths
contains exactly one nonempty lower-face segment. Fix its upper prefix
and upper suffix, either of which may be absent. Suppose that all these
upper pieces are induced and that distinct upper pieces are disjoint
and nonadjacent. Then the two replacements are induced, disjoint and
nonadjacent precisely when their lower segments are induced, disjoint
and nonadjacent, and every equality between an upper projection and a
lower vertex is one of the prescribed vertical joining pairs of that
same replacement. If a replacement has $w$ edges and $u$ upper vertices,
its lower segment has $w-u$ edges.
\end{proposition}
\begin{proof}
There are $w+1-u$ lower vertices, proving the length formula. Pairs of
vertices in the same face are covered by the stated inducedness and
separation conditions. Across opposite faces, adjacency is equality of
the projections; exactly the prescribed endpoint equalities are allowed.
This accounts for every pair within and between the replacements.
Compatibility with retained outside vertices is a separate requirement
enforced by their prepared domains and the fixed joining edges.
\end{proof}

Crossing parity equals the difference of the endpoint faces. A path
with zero crossings stays in its anchor face, which must therefore
contain at least 46 allowed vertices. Applying these two necessary
conditions and the total crossing budget leaves 154 contexts with a
unique allocation of crossings between the two replacements:
\[
\begin{array}{c|rrrr}
\text{allocation}&(0,1)&(0,2)&(1,1)&(1,2)\\\hline
\text{contexts}&16&24&78&36
\end{array}
\]
In each case the number of crossings of a replacement equals its number
of upper anchors. Each replacement thus has exactly one lower segment,
so Proposition~\ref{prop:twofixedupper228} applies. The remaining thirteen
contexts admit other allocations and are searched directly in $Q_9$.

The completed width-44 exclusion supplies an additional necessary
condition at width 45. If each replacement retained either old neighbour
of one of its anchors, shortening that end of each interval would give
a width-44 representation of the same complete candidate. The blockers
of the appended vertex must remain changed, so the shortened intervals
belong to the covered family. Consequently at least one replacement
must omit both old anchor neighbours. This implication uses the native
width-44 result as a premise; it does not transfer that exclusion upward
without further work.

Complete upper-piece enumeration gives 2,141 configurations. Splitting
each according to which replacement omits both old neighbours gives
4,282 branches. Fixed upper vertices or lower anchors invalidate 3,527
branches; necessary lower-domain connectivity removes 83 more. The
remaining 672 configurations form 392 exact lower-task groups and
331 representatives after domain containment. The boundary condition
has already been imposed in the domains before grouping, so no residual
condition is lost. Sixty-nine of the 154 contexts have no surviving
configuration. All 331 representative queries are natively infeasible;
ten required a longer run after an initial timeout.

The complete cover is
\[
\underbrace{107}_{\text{initial geometry}}+
\underbrace{34}_{\text{initial completed queries}}+
\underbrace{69+85}_{\text{upper-piece reduction}}+
\underbrace{13}_{\text{direct queries}}=308.
\]
The initial batch was interrupted by low available memory. Only its 34
already completed infeasibility results were retained; no running,
unknown or unattempted case was treated as excluded. The thirteen
direct queries also terminate as infeasible. Every accepted infeasible
query in this round did so at its first solve, without cycle cuts.
The 154 literal allocation records and their arithmetic implication
passed Lean kernel checks. Extraction of those records, enumeration,
domain necessity, cover assembly and the numerical contradictions remain
native computations. In the concrete upper templates there are no
unintended projection contacts at a lower anchor; reuse on other data
must distinguish actual vertical joining endpoints from other anchors.

Padding smaller replacements with unchanged original vertices extends
the cover to two blocks of at most 45 edges each. This excludes the
specified fixed-seed, endpoint-24, length-preserving construction with
four crossings. It supplies no new snake or global upper bound.
Wider blocks and different seeds or endpoints remain construction
possibilities~\cite{research228}.

'''
short=r'''The restricted exclusion now covers two replacement blocks of at most
45 edges for the chosen seed and appended vertex 24. The 308 maximal
contexts retain all outside vertices and both pairs of anchors, preserve
the two block lengths, and require four crossings of the chosen coordinate.

The reduction fixes the short induced upper-face pieces before searching for
the two long lower-face paths in $Q_8$. The lower paths must be induced,
disjoint and nonadjacent. Across opposite faces, adjacency occurs exactly
when the eight remaining coordinates agree. Therefore a lower path may
meet an upper projection only at its intended vertical joining endpoint;
it must avoid all upper projections belonging to the other replacement.
Together with separation of the upper pieces, these conditions account
for every possible repetition or chord. A replacement with $w$ edges
and $u$ upper vertices needs a lower segment of $w-u$ edges.

Endpoint faces determine whether the crossing count is even or odd.
Zero crossings is impossible if the anchor face has fewer than the
required 46 allowed vertices. These observations force the allocations
$(0,1)$, $(0,2)$, $(1,1)$ or $(1,2)$ in 154 contexts. Each replacement
then has exactly one lower segment. The other thirteen contexts are
searched directly because their crossing arrangements are different.

The width-44 result also constrains width 45. If each replacement kept
an old anchor neighbour, one could shorten that end of each interval
and obtain the same candidate in the excluded width-44 family. At least
one replacement must therefore omit both old anchor neighbours.
This deduction retains the computational dependency on the width-44 cover.

Enumerating the upper pieces gives 2,141 configurations. Imposing the
boundary condition and necessary lower-domain connectivity leaves 672.
They give 392 exact tasks and 331 representatives after domain containment.
Sixty-nine contexts have no surviving configuration; all 331 remaining
representative queries return infeasibility, covering the other 85
reduced contexts. Thirteen direct queries also return infeasibility.
Together with 107 initial geometric exclusions and 34 completed initial
queries, this accounts for all 308 contexts. The initial batch was
interrupted by low available memory; only completed infeasibility rows
were retained. Timeouts and incomplete rows supplied no exclusions.

Lean checked the arithmetic for the 154 literal crossing-allocation
records. The general joining arguments reuse earlier checked constructors.
The extraction of the records, finite enumeration, prepared domains,
cover assembly and solver contradictions retain their separate native
status. No 192-edge witness or global optimality result follows from
this fixed construction family~\cite{research227,research228}.

'''
bib=r'''\bibitem{research228}
I.~Hironaka, T.~Ma, and S.~Zhan. \emph{Two lower-dimensional replacement
paths and the width-45 construction cover}. Research milestone 228,
15 November 2026.
\url{https://github.com/hironaka-iori/Snake-in-the-box-in-9/tree/main/milestones/228-wider-replacement-constructions}.

'''
for name in ['snake9_research.tex','snake9_frontier_explanation.tex']:
    p=D/name;before=(H/'data'/(name+'.before.txt')).read_bytes();assert p.read_bytes()==before
    text=before.decode('utf-8').replace('Research state after round 227','Research state after round 228')
    if name=='snake9_research.tex':
        old='two-block search through length 44 is excluded natively. Fixing small\nupper-face portions reduces the final 42 cases to 57 lower-dimensional\npath-pair queries, all infeasible.'
        assert old in text
        text=text.replace(old,'two-block search through length 45 is excluded natively. Fixing small\nupper-face portions and using crossing parity reduces 154 width-45\ncontexts to lower-dimensional tasks; direct queries cover thirteen\nadditional cases, completing the 308-context cover.',1)
        anchor=r'\section{Verification scope and remaining problem}\label{sec:verification}'
        assert text.count(anchor)==1;text=text.replace(anchor,section+anchor,1)
        anchor='The round-220 full-source review corrects historical proof references,'
        text=text.replace(anchor,'Section~\\ref{sec:width45} extends the native cover to width 45.\nThe 154 crossing-allocation records have kernel-checked arithmetic;\nall finite reduction and solver dependencies remain explicit.\n'+anchor,1)
    else:
        text=text.replace('milestones through round 227','milestones through round 228')
        start=text.index('The restricted exclusion now covers two replacement blocks of at most')
        end=text.index(r'\section{Remaining questions}',start);text=text[:start]+short+text[end:]
        text=text.replace('excludes widths through 44 for the chosen','excludes widths through 45 for the chosen',1)
    text=text.replace(r'\end{thebibliography}',bib+r'\end{thebibliography}',1)
    p.write_bytes(text.encode('utf-8'));(R/'paper'/name).write_bytes(p.read_bytes())
print('UPDATED_EXISTING_MANUSCRIPTS228')
