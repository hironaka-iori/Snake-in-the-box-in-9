"""Update existing manuscripts with simultaneous replacement logic."""
from pathlib import Path
import hashlib,json,re
H=Path(__file__).resolve().parents[1];R=H.parents[1];D=Path('D:/Codex/2026-10-13/new-chat/outputs')
def once(s,a,b):assert s.count(a)==1,a[:80];return s.replace(a,b,1)
summary=json.loads((H/'data/search-summary.json').read_bytes())
assert summary['short_family_excluded'] and summary['long_family_statuses']=={'STATIC_EXCLUDED':107,'INFEASIBLE':102,'UNKNOWN':92}
for name in ['TwoBlocks224','TwoBlockEscape224']:assert json.loads((H/'data'/(name+'-audit.json')).read_bytes())['status']=='PASS'
section=r'''\subsection{Interaction between simultaneous replacements}
\label{sec:twoblock224}
Replacing two separated parts of a path at once can avoid an obstruction
that prevents performing the same changes successively.

\begin{proposition}[Necessary interaction between replacements]
\label{prop:interaction224}
Let $\mathcal B$ be a family of equal-length induced paths, closed under
every length-preserving replacement of one block of at most $K$ edges.
Suppose no member admits an endpoint extension. Let $P\in\mathcal B$
and let $Q$ be an induced path of the same length, agreeing with $P$
outside two open index intervals $(a,b)$ and $(c,d)$, where
$a\le b\le c\le d$ and $b-a,d-c\le K$.
If $Q$ admits an endpoint extension, then some new interior vertex of
each block equals or is adjacent to an original interior vertex of
the other block.
\end{proposition}
\begin{proof}
Suppose the new first interior is disjoint and nonadjacent to the
original second interior. Apply only the first change. Pairs entirely
outside that block retain their relationships from $P$; pairs inside
it have their relationships from $Q$. Every remaining pair either
agrees with $Q$ or lies between the new first interior and the old
second interior, where the assumed separation applies. The intermediate
path is therefore induced. The two replacements can now be performed
successively, so closure places $Q$ in $\mathcal B$, contradicting its
extension. Reversing the order gives the other required contact.
\end{proof}
The intermediate-path construction and the conditional implication
have passed Lean for actual indexed paths. Equality counts as contact:
a vertex can move from one old block into the other new block. The
argument uses original positional interiors, not merely the vertices
absent from the final path. Applying it with $K=33$ uses the earlier
native bank-closure census; no closure through 44 edges is assumed.

\paragraph{Two separated regions for endpoint 24.}
The chosen seed ends at 88. Appending 24 requires removal of its other
selected neighbours, $p_7=28$ and $p_{143}=56$. Consider two
length-preserving replacements containing these positions strictly
inside their respective blocks, retaining all other positions and
then appending 24. For blocks of at most 33 edges, every such pair is
contained in one of the 224 maximal pairs
\[
[a,a+33],\ [c,c+33],\qquad
0\le a\le6,\quad111\le c\le142.
\]
Padding with unchanged vertices preserves any valid shorter replacement.
The first replacement has no crossing in coordinate 8 and the second
has one: the unchanged portions already contain three required crossings,
and the second pair of anchors lies in opposite faces.

Each replacement avoids retained vertices, neighbours of retained
non-anchor vertices, and the new endpoint and its neighbours; its own
anchors are restored. Non-anchor vertices with fewer than two available
neighbours can be removed repeatedly. Connectivity, size and parity
give further necessary restrictions. The two new replacement paths
must also be disjoint and nonadjacent to each other. Any proposed
193-vertex concatenation is checked before accepting a witness.

For the 33-edge family, geometry excludes 171 maximal contexts and
native solver queries exclude the other 53. A final run omits the
interaction restriction entirely, so this numerical exclusion does
not depend on the bank-closure premise. It has no complete Lean
contradiction certificate. For 44-edge blocks, the 301 maximal contexts
give 107 geometric exclusions, 102 solver exclusions and 92 unresolved
cases. These models impose only the combined crossing count and use
no interaction restriction or short-move closure premise.

Reducing the 92 unresolved domains to their anchor-to-anchor
biconnected block chains removed no vertex, so no unchanged rerun was
made. Sixteen selected contexts were then strengthened by connectivity
flows. An actual 44-edge path supports these constraints by sending
$44,43,\ldots,1$ units along its successive oriented edges: the root
supplies 44 units and every other selected vertex receives one net unit.
All 16 remain unknown, leaving 92 unresolved contexts. No new snake or
global bound is obtained~\cite{research224}.

'''
frontier=r'''\subsection{Why simultaneous changes must interact}
Suppose a family is closed under individual length-preserving block
replacements of at most $K$ edges, and none of its paths can be extended.
A simultaneous change of two such blocks can enable extension only if
each new interior equals or is adjacent to some original interior vertex
of the other block. Otherwise the noninteracting replacement can be
performed first, followed by the other; closure would keep the final
path in the blocked family. The actual intermediate-path construction
and this conditional implication have now passed Lean.

Appending endpoint 24 to the chosen seed requires changing positions
7 and 143, whose original vertices are 28 and 56. All pairs of blocks
of at most 33 edges containing those positions are covered by 224
maximal window pairs. Geometry excludes 171 and native solver queries
exclude the other 53, even without imposing the interaction condition.
Thus this particular route is computationally closed without relying
on the earlier closure census. Its solver contradictions are not checked
in Lean.

Allowing 44-edge blocks gives 301 maximal contexts: 107 are geometrically
excluded, 102 are solver-excluded and 92 remain unresolved. Connectivity
flows did not resolve 16 selected retries. These results concern the
fixed seed, fixed outside indices, endpoint 24 and four crossings.
They give no global optimality conclusion; larger or differently
arranged changes remain possible~\cite{research224}.

'''
bib=r'''\bibitem{research224}
I.~Hironaka, T.~Ma, and S.~Zhan. \emph{Interaction between simultaneous
replacements and two-region construction searches}.
Research milestone 224, 15 November 2026.
\url{https://github.com/hironaka-iori/Snake-in-the-box-in-9/tree/main/milestones/224-cross-block-reconnections}.

'''
records={}
for name in ['snake9_research.tex','snake9_frontier_explanation.tex']:
    before=(H/'data'/(name+'.before.txt')).read_bytes();assert (D/name).read_bytes()==before and (R/'paper'/name).read_bytes()==before
    s=before.decode('utf-8');s=once(s,'Research state after round 223','Research state after round 224')
    if name=='snake9_research.tex':
        s=once(s,r'\section{Verification scope and remaining problem}',section+r'\section{Verification scope and remaining problem}')
        s=once(s,'larger neighbourhoods remain unresolved, with no new construction.',
               'larger neighbourhoods remain unresolved, with no new construction.\nA checked interaction theorem explains when simultaneous block changes\ncan escape a family closed under separate changes. A complete restricted\ntwo-block search through length 33 is excluded natively; longer blocks\nretain unresolved cases.')
        s=once(s,'The round-220 full-source review corrects historical proof references,',
               'Section~\\ref{sec:twoblock224} adds checked simultaneous-replacement\nlogic. The finite two-region exclusions remain native, with complete\ncoverage recorded separately from unresolved cases.\nThe round-220 full-source review corrects historical proof references,')
    else:
        s=once(s,r'\section{Remaining questions}',frontier+r'\section{Remaining questions}')
        s=s.replace('milestones through round 223','milestones through round 224')
    s=once(s,r'\end{thebibliography}',bib+r'\end{thebibliography}')
    assert re.search(r'\\author\{[^\n]*',s).group()==re.search(r'\\author\{[^\n]*',before.decode('utf-8')).group()
    if name=='snake9_research.tex':assert re.search(r'\\hypersetup\{.*?\n\}',s,re.S).group()==re.search(r'\\hypersetup\{.*?\n\}',before.decode('utf-8'),re.S).group()
    after=s.encode('utf-8');(D/name).write_bytes(after);(R/'paper'/name).write_bytes(after)
    records[name]=dict(before_sha256=hashlib.sha256(before).hexdigest(),after_sha256=hashlib.sha256(after).hexdigest())
(H/'data/manuscript-edits.json').write_text(json.dumps(records,indent=2)+'\n',encoding='utf-8')
print('UPDATED_EXISTING_MANUSCRIPTS')
