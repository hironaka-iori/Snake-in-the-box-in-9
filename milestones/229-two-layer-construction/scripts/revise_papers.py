"""Update the two existing manuscripts from the completed round-229 evidence."""
from pathlib import Path
import json
H=Path(__file__).resolve().parents[1];R=H.parents[1];D=Path('D:/Codex/2026-10-13/new-chat/outputs')
def read(p):return json.loads(p.read_bytes())
assert read(H/'data/coverage46.json')['status']=='COMPLETE_NATIVE_EXCLUSION'
for name in ['ProjectionPorts229','CrossingAllocation229']:assert read(H/'data'/(name+'-audit.json'))['status']=='PASS'
free=read(H/'data/free-summary.json');remaining=len(free['unresolved'])
frontier=(f"The search with unrestricted crossing count excludes {315-remaining} of the\n315 maximal contexts and leaves {remaining} unresolved." if remaining else
"The search with unrestricted crossing count now excludes all 315 maximal\ncontexts. Padding includes smaller blocks in this same family.")
section=r'''\subsection{Exact projection restrictions and variable crossing counts}
\label{sec:projection229}
The projection restriction can be stated independently of the dimension.
Let $D$ be a lower-face domain, $U$ the projections of the replacement's
own upper pieces, $P$ its intended vertical joining projections, and $O$
the projections of upper pieces belonging to other replacements. The
correct filtered domain is
\[
D\setminus\bigl((U\setminus P)\cup O\bigr).
\]
Membership says exactly that an own upper adjacency is possible only
at a prescribed joining projection, and that no adjacency to another
replacement's upper vertices is possible. This follows because adjacency
between the two faces is equality of the lower coordinates.

For a single crossing, suppose two actual induced paths have equal
projected joining endpoints. The filtered-domain condition with that
one exemption is equivalent to the exact indexed compatibility of the
joining constructor. Indeed, any common projection must equal the
exempted endpoint. Injectivity of each path then fixes both indices,
so no additional joining edge occurs. Conversely, exact compatibility
permits only this coincidence. If the lower segment has positive length,
its fixed opposite endpoint differs from the joining endpoint and cannot
be exempted. The zero-length case is different because the two endpoints
coincide. These general statements have passed Lean kernel checks.
For two crossings, the two actual joining equalities and separation of
the upper pieces remain necessary, as in Proposition~\ref{prop:twofixedupper228}.

The crossing-allocation argument also admits a general arithmetic proof.
Let $A,B\in\{0,1,2\}$ count the upper anchors of two replacements, and let
$a,b$ be their crossing counts. Suppose
\[
a\equiv A\pmod2,\qquad b\equiv B\pmod2,
\qquad a+b=A+B,
\]
and require $a>0$ when $A=2$, and $b>0$ when $B=2$.
Then $a\ge A$ and $b\ge B$: targets zero and one follow from
nonnegativity and parity; target two follows from positive evenness.
Equality of the totals forces $a=A$ and $b=B$. This implication has
passed Lean for arbitrary natural counts. In the construction, endpoint
faces supply parity, and an insufficient upper-face domain excludes
zero crossings when both anchors are upper. Extraction of these premises
from each finite domain is a separate calculation.

At width 46 the first interval starts at $0,\ldots,6$ and the second at
$98,\ldots,142$, giving 315 contexts. Initial necessary geometry excludes
106. The preceding width-45 four-crossing cover supplies the boundary
condition for the four-crossing search. The remaining contexts comprise
185 with allocations $(0,1),(0,2),(1,1),(1,2)$ in counts
$20,13,100,52$, and 24 with other allocations.
Complete upper enumeration gives 3,535 configurations. After imposing
the boundary condition, 5,866 fixed-neighbour contradictions and 318
disconnections remove branches; 886 survive, forming 538 exact groups
and 496 representatives. One representative is contained in a previously
excluded task, while 495 new native queries are infeasible. Eight required
longer runs after initial timeouts. The direct queries exclude all 24
other contexts. Thus
\[
106+\underbrace{89+96}_{185\text{ reduced contexts}}+24=315.
\]
This completes the native four-crossing exclusion through width 46.
The corrected filter exempts only actual joining projections throughout
the new preparation. The finite enumeration and numerical contradictions
remain outside the Lean proofs above.

The crossing restriction was then removed from the construction search.
An intermediate six-crossing search returned 200 infeasibility results
and nine timeouts among the 209 nonstatic contexts. It used no boundary
condition inherited from the four-crossing family. A subsequent model
prescribed no total crossing count, while retaining the same intervals,
anchors, outside positions and length requirements. Its crossing-parity
variables are bounded by the available vertical edges, so the former
four-crossing budget imposes no hidden cap.

Completed exclusions can strengthen this larger search. If $f$ counts
unchanged crossings and $c$ counts crossings inside the two replacements,
the complete same-context four-crossing cover forbids $f+c=4$.
In each of the 200 contexts excluded at six crossings, it also forbids
$f+c=6$. The nine unresolved six-crossing contexts receive no such
six-count restriction. These deductions preserve every actual candidate
under the explicit native premises, even though they can remove
disconnected-cycle solutions of the degree relaxation.

@FREE_FRONTIER@
All nine initially unresolved six-crossing contexts are excluded by these
broader queries, which imposed no six-count exclusion on those nine.
Consequently the same construction family is now excluded at six
crossings as well. Each of the eleven remaining unrestricted contexts
permits a total of two crossings at the level of parity and face capacity:
four force replacement allocation $(0,0)$ and seven force $(1,0)$.
These give the next lower-dimensional construction targets. They supply
no witness, and counts of eight or more remain possible in the unresolved
family.
Every timeout remains unresolved until separately excluded. These
calculations concern the fixed seed, appended endpoint 24 and two
length-preserving blocks; they give no new snake or global upper bound.
The general projection and allocation implications are kernel checked;
finite extraction, cover assembly and solver exclusions retain their
native status~\cite{research229}.

'''.replace('@FREE_FRONTIER@',frontier)
short=r'''The four-crossing construction is now excluded through two replacement
blocks of 46 edges. All 315 maximal contexts are covered: 106 by initial
geometry, 185 by fixing the upper pieces, and 24 by direct search. In
the reduced group, 89 contexts have no compatible upper configuration.
The other 96 reduce to 496 path-pair tasks: one is contained in an earlier
excluded task and 495 are newly excluded. Eight initial timeouts required
longer runs. These remain native computational conclusions. The
four-crossing reduction uses the preceding native width-45 cover as the
premise of its boundary-change condition.

The exact reason for the projection restriction is simple. Across the
two layers, vertices are adjacent precisely when all other coordinates
agree. A lower path must avoid projections of its own upper pieces
except at its actual joining endpoints, and must avoid all projections
of the other replacement's upper pieces. A fixed endpoint that does not
join the upper layer has no exemption. For a single crossing,
the intended endpoint equality and injectivity of both paths make this
restriction equivalent to the exact joining condition. Lean checked
that equivalence and the positive-length fixed-endpoint consequence.

There is also a general crossing-allocation argument. Let $A,B$ be the
numbers of upper anchors of the replacements, each between zero and two,
and let $a,b$ be their crossing counts. Endpoint faces give
$a\equiv A\pmod2$ and $b\equiv B\pmod2$. If the upper face is too small
to hold a replacement with two upper anchors, zero crossings is excluded.
Then $a\ge A$ and $b\ge B$: a target of two requires a positive even
count, and a target of one requires an odd count. If the total budget
is $A+B$, both inequalities must be equalities. Lean checked this
arithmetic implication for arbitrary natural counts. The finite input
conditions still require their separate domain calculation.

To investigate whether fixing four crossings was obstructing construction,
the same 315 contexts were examined with more freedom. The six-crossing
query excluded 200 of the 209 nonstatic cases and left nine unresolved.
The next model left the total crossing count free. It kept the same
seed, endpoint 24, two block lengths and retained outside vertices, and
used no boundary restriction from the earlier four-crossing family.

The earlier results still provide valid count exclusions in each matching
context: total four is impossible, and total six is impossible in the
200 cases with completed six-crossing results. Adding these exclusions
to the larger model removes only cases already covered by native evidence.
@FREE_FRONTIER@
All nine earlier six-crossing unknowns are now excluded by the broader
queries, so the exact-six family is also completely covered. In the
eleven remaining unrestricted cases, a total of two crossings would
force replacement allocations $(0,0)$ in four cases and $(1,0)$ in seven.
This is the next construction route. It is only a necessary allocation
calculation; a compatible pair of paths still has to be found or excluded.
Even totals of at least eight also remain possible in the unresolved family.
This is a construction-family result, with no new snake or global
optimality claim. Numerical exclusions, enumeration and data extraction
remain separate from the checked general implications~\cite{research229}.

'''.replace('@FREE_FRONTIER@',frontier)
bib=r'''\bibitem{research229}
I.~Hironaka, T.~Ma, and S.~Zhan. \emph{Exact projection restrictions and
variable-crossing replacement constructions}. Research milestone 229,
15 November 2026.
\url{https://github.com/hironaka-iori/Snake-in-the-box-in-9/tree/main/milestones/229-two-layer-construction}.

'''
for name in ['snake9_research.tex','snake9_frontier_explanation.tex']:
    p=D/name;before=(H/'data'/(name+'.before.txt')).read_bytes();assert p.read_bytes()==before
    text=before.decode('utf-8').replace('Research state after round 228','Research state after round 229')
    if name=='snake9_research.tex':
        old='two-block search through length 45 is excluded natively. Fixing small\nupper-face portions and using crossing parity reduces 154 width-45\ncontexts to lower-dimensional tasks; direct queries cover thirteen\nadditional cases, completing the 308-context cover.'
        assert old in text
        text=text.replace(old,'two-block four-crossing search through length 46 is excluded natively.\nGeneral projection-filter and crossing-allocation implications have passed\nLean. The wider search also permits arbitrary crossing counts; its\nremaining scope and dependencies are stated explicitly.',1)
        anchor=r'\section{Verification scope and remaining problem}\label{sec:verification}';assert text.count(anchor)==1
        text=text.replace(anchor,section+anchor,1)
        anchor='The round-220 full-source review corrects historical proof references,'
        text=text.replace(anchor,'Section~\\ref{sec:projection229} adds general kernel-checked projection\ncompatibility and crossing-allocation implications, a native width-46\nfour-crossing cover, and a search without a prescribed crossing count.\nThe computational exclusions retain their stated native dependencies.\n'+anchor,1)
    else:
        text=text.replace('milestones through round 228','milestones through round 229')
        start=text.index('The restricted exclusion now covers two replacement blocks of at most')
        end=text.index(r'\section{Remaining questions}',start);text=text[:start]+short+text[end:]
        text=text.replace('The completed two-block search excludes widths through 45 for the chosen\nendpoint and seed. Wider blocks, another endpoint or another seed are\nthe next construction choices.',
            'The four-crossing two-block search excludes widths through 46 for the\nchosen endpoint and seed. The unrestricted-crossing search has the scope\nand remaining cases stated above. Wider blocks, different seeds or\nendpoints, and changed block lengths remain construction choices.',1)
    text=text.replace(r'\end{thebibliography}',bib+r'\end{thebibliography}',1)
    p.write_bytes(text.encode('utf-8'));(R/'paper'/name).write_bytes(p.read_bytes())
print('UPDATED_EXISTING_MANUSCRIPTS229')
