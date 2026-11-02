"""Revise the open manuscript from an exact backup; preserve unrelated content."""
from pathlib import Path
import hashlib, json, zipfile

HERE=Path(__file__).resolve().parents[1]
ROOT=HERE.parents[1]
EDITOR=Path('D:/Codex/2026-10-13/new-chat/outputs/snake9_research.tex')
MIRROR=ROOT/'paper/snake9_research.tex'
sha=lambda b:hashlib.sha256(b).hexdigest()
for name in ['data','audit','logs']:(HERE/name).mkdir(exist_ok=True,parents=True)
backup=HERE/'data/paper-before.zip'
if not backup.exists():
    raw=EDITOR.read_bytes()
    assert raw==MIRROR.read_bytes()
    assert sha(raw)=='7d4d974bc353ca723e4a5362b0960610d959dfe622b115b629968818c178875c'
    with zipfile.ZipFile(backup,'w',zipfile.ZIP_DEFLATED) as z:
        info=zipfile.ZipInfo('snake9_research.tex',(1980,1,1,0,0,0))
        info.compress_type=zipfile.ZIP_DEFLATED;z.writestr(info,raw)
with zipfile.ZipFile(backup) as z:raw=z.read('snake9_research.tex')
old=raw.decode('utf-8').replace('\r\n','\n');s=old
def replace(a,b):
    global s
    assert s.count(a)==1,(s.count(a),a[:100])
    s=s.replace(a,b)
def between(a,b,new):
    global s
    first=s.index(a);last=s.index(b,first)
    s=s[:first]+new+'\n\n'+s[last:]

between(r'\begin{abstract}',r'\clearpage',r'''\begin{abstract}
Let $a(9)$ be the maximum edge length of an induced path in the nine-dimensional binary hypercube. An explicit construction and an archived contributor proof give $191\le a(9)\le235$; a complete independent rebuild of the upper-bound proof remains pending. The square census and six-centre count estimate give $39m+2s_0\le9200$, where $m$ counts path edges and $s_0$ counts empty coordinate squares. We retain the empty-square term through integer shares. Checked local inequalities, overlap accounting and exact finite coverage connect each snake to a weighted state walk, assuming refutations for a specified catalogue of 1378 local patterns. Its total weight satisfies $W+4200m\le1098960$. A potential of slope $p$ and range $R$ would then give $(4200+p)m\le1098960+8p+R$. The completed local-share profile uses $(p,R)=(483,551)$ and recovers 235. Five additional share bounds, together with the full potential certificate for $(496,602)$, would give 234. On the fixed comparison graph, the least sufficient integer floors within the original target box are $(16,18,16,16,16)$; the second target is reduced from 20 to 18. Exact numerical checks cover every graph edge, while the corresponding Lean certificate batch remains incomplete. Cycle and open-walk obstructions explain the limits of changing only local floors or potential parameters. The exact optimum, including the conjecture 196, remains unresolved.
\end{abstract}''')
replace('Section~\\ref{sec:current-model} constructs the actual state sequence, proves the completed filter and history-credit implications, and states the remaining graph-coverage premises. It then compares the finite weighted graphs and proves the limits of changing their slope and potential range.',
        'Section~\\ref{sec:current-model} proves graph coverage and the complete weight interpretation, under the exact reference-catalogue premise. It then derives the upper-bound implications, identifies the least sufficient pending floors in the fixed model, and explains the limits of changing the potential parameters.')
replace(r'Conditional bound 234 & Mean 496, range 600 and boundary contribution 21; five local shares and the remaining graph proof are pending.\\',r'Conditional bound 234 & Slope 496, range 602 and boundary contribution 21; five local shares, the reference refutations and the full potential certificate remain pending.\\')
replace(r'History credits and graph interfaces & All 55 history-share rules are justified; finite graph coverage and the global potential retain explicit obligations.\\',r'Graph interpretation and total charge & Complete coverage and all weight components are checked. The actual-walk implication retains the exact 1378-key reference premise.\\')
replace('The count-filter implications are now connected to actual windows; the reference family retains two explicit closed catalogue premises in the current checking environment. The 55 remembered-window share rules now have complete geometric interpretation. Finite coverage of the accepted-key graph and the remaining weight components are addressed separately below~\\cite{currentarchive,interfacearchive,historycreditarchive}.',
        'The count-filter implications are connected to actual windows. The new proof chain assumes refutations only for the exact 1378-key reference union. Complete graph coverage, the 55 remembered-window rules and every other weight component have passed their checks. The full finite potential and the reference refutations remain separate obligations~\\cite{currentarchive,interfacearchive,historycreditarchive,weightintegrationarchive,referenceunionarchive}.')
replace('The stronger nine-shape target is displayed below. Its status column refers to the stated target, so the completed share of twelve for $012345$ does not certify its proposed value sixteen.',
        'The original nine-shape target is displayed below. Its status column refers to that target, so the completed share of twelve for $012345$ does not certify sixteen. Section~\\ref{sec:least-floors} reduces the required $012034$ floor from 20 to 18; the weaker target still needs a local proof.')
replace('The conditional catalogue therefore retains precisely the five pending targets shown above.',
        'Five local shapes therefore remain unresolved. The current conditional argument uses floor 18 for $012034$ and the displayed targets for the other four pending shapes.')

between('For the reference family, let $\\mathcal F_{235}$',r'\subsection{Complete interpretation of the remembered share rules}',r'''For the reference family, let $\mathcal F_{235}$ contain the 1287 keys of
the six-centre catalogue, and let $\mathcal F_{236}$ contain the 732 keys
of the earlier radius-four catalogue. A key consists of a canonical direction
word and its internal count symbols. Their union is taken after joint
reversal and coordinate relabelling. The remaining assumption is that each
of its 1378 local necessary-condition systems has a refutation.

\begin{proposition}[Conditional reference retention]\label{prop:reference-union-retention}
Assume every local system in the exact reference union is refuted. Every
actual candidate transition avoids this family in both orientations. The union has
\[
1287+732-641=1378
\]
keys and 2678 distinct oriented direction-and-count pairs. For a key with
$w$ count symbols, where $2\le w\le6$, every offset $s$ with $s+w\le6$
is covered.
\end{proposition}
\begin{proof}
The exact union takes the 1287 keys of $\mathcal F_{235}$ and 91 additional
keys of $\mathcal F_{236}$. Checked source indices identify every chosen
representative. Each has $w+1$ directions and $w$ symbols in $\{1,\ldots,6\}$.

At offset $s$, the extracted count code is
\[
\left\lfloor\frac{\widehat c_r}{6^{6-s-w}}\right\rfloor\bmod6^w.
\]
Uniqueness of a fixed-length base-six expansion identifies its digits with
$b_{r+s+3},\ldots,b_{r+s+w+2}$. The matching directions start at $r+s+2$.
A symbol below six gives equality to the actual count; six gives the full
interval $[6,21]$. A hypothetical match, after translation and coordinate
normalization, therefore realizes the local system for a key in the union.
Its assumed refutation is a contradiction. Reversal reverses both lists and
preserves the argument. This deduction and its use in the complete filter
have passed Lean~\cite{referenceunionarchive}. The checks identify the required
keys and prove the implication; they do not supply their refutations.
\end{proof}''')

replace('This theorem supplies the remembered-window component of the edge credit.\nIt does not identify all other credit components or verify the full graph\npotential. Those are separate requirements of the global argument.',
        'This theorem supplies the remembered-window component. The remaining\ncomponents and their maximum are connected to the same five centres in\nTheorem~\\ref{thm:actual-weight-budget}; the full potential is a separate check.')
between(r'\begin{proposition}[Conditional coverage of actual state walks]',r'\subsection{Completed local bounds and conditional comparisons}',r'''\begin{proposition}[Coverage of actual state walks]\label{prop:defined-graph-walk}
Assume every local system in the exact reference union is refuted. Every
$m$-edge snake with $m\ge9$ gives a walk of $m-8$ edges in the graph just
described. The row at each step has the actual direction, history and
six-count key, and its endpoints are the states of
Proposition~\ref{prop:actual-state-sequence}.
\end{proposition}
\begin{proof}
The actual candidate key at each fitting window has bounded direction,
history and count indices. Propositions~\ref{prop:local-filter-retention},
\ref{prop:history-exclusion-retention} and
\ref{prop:reference-union-retention} show that it passes every numeric test.

For each of the 791 compatible direction/history pairs, a finite partition
covers all six-count codes. Each part is either accepted by the assigned
diagram root or lies in a product of six integer intervals whose vectors
trigger an exclusion. A code passing all tests cannot lie in a rejected
part, so its full key is accepted. There are 127 shared coverage classes.
All their partitions, context-specific exclusion checks and final assembly
have passed Lean. The assignment of all $505\cdot75=37875$ bounded pairs,
including the three history-dependent overrides, is also checked
~\cite{graphcoveragearchive,weightintegrationarchive}.

The graph enumerates every bounded accepted key, so it contains the actual
row. Its endpoints use the direction slices, history update and count shift
of the actual state sequence. Consecutive rows therefore share the same
intermediate state. The strengthened statement retains one common row
index for the full key and both endpoints; this identifies the weight even
when parallel rows have equal endpoints. There are $m-8$ fitting windows.
The whole implication from the exact reference union has passed Lean
~\cite{referenceunionarchive}.
\end{proof}

\subsection{Complete edge weights and total charge}\label{sec:actual-weights}
At a fitting window beginning at $r$, let $L_r$ be the maximum of all
applicable lower bounds on the shares at $x_{r+4},\ldots,x_{r+8}$, together
with zero. The alternatives are the nine-direction geometric bound, the
remembered-window rules, four count-conditioned rules and their reversals,
the share-120 rule, and the chosen count-independent floor. The two current
floor choices are:
\begin{center}\small
\begin{tabular}{c r r}
\toprule
Six-transition shape & Completed floor & Conditional floor\\\midrule
$012031$ & 16 & 16\\
$012032$ & 0 & 16\\
$012034$ & 0 & 18\\
$012301$ & 0 & 16\\
$012304$ & 16 & 16\\
$012310$ & 12 & 12\\
$012314$ & 16 & 16\\
$012340$ & 0 & 16\\
$012345$ & 12 & 16\\\bottomrule
\end{tabular}
\end{center}
A zero floor contributes no additional count-independent estimate. All other
applicable bounds remain in the maximum. The conditional choice assumes the
five unfinished local bounds of $16,18,16,16,16$ in the order
$012032,012034,012301,012340,012345$.

\begin{theorem}[Actual edge weight and total charge]\label{thm:actual-weight-budget}
For the completed floor choice, every fitting window of a snake satisfies
\[
w_r=120b_{r+8}+L_r
\le120\alpha_{r+8}+\sum_{j=4}^{8}\sigma_{12}(x_{r+j}).
\]
For $m\ge9$, its total weight $W=\sum_{r=0}^{m-9}w_r$ satisfies
\[
W+2520\le5G_{12},\qquad W+4200m\le1098960.
\]
The same statements hold for the conditional floor choice under the five
local share bounds just stated. Neither total-weight assertion requires
the reference-catalogue premise.
\end{theorem}
\begin{proof}
The geometric table covers all 505 nine-direction shapes, with 357 positive
bounds and 148 zeros. Its checked coordinate transfers charge the five
positions $r+4,\ldots,r+8$. Theorem~\ref{thm:history-share-complete} supplies
the same assertion for every remembered rule. The count-conditioned,
share-120 and count-independent rules use the final six-transition segment
beginning at $r+3$, so they charge these same five internal vertices.
Reversal reverses both the directions and the five count symbols. A count
symbol six retains the full interval $[6,21]$ throughout.

Each applicable bound is at most the same five-centre share sum; their
maximum with zero is therefore at most that sum. Since
$b_{r+8}\le\alpha_{r+8}$, the local weight inequality follows. The exact
interpretation of the finite weight expression, including every component,
has passed Lean for both floor choices with the stated premises
~\cite{weightintegrationarchive}.

The omitted singleton positions are $0,1,\ldots,7,m$. The two endpoint
bounds, three adjacent-pair bounds and remaining positive count give
\[
\sum_{r=0}^{m-9}\alpha_{r+8}+21\le T.
\]
Each share occurs at most five times. Summing the local inequality yields
$W+2520\le120T+5\Sigma=5G_{12}$. Finally,
$5G_{12}+4200(m+1)\le1105680$ gives $W+4200m\le1098960$.
These summations and the actual-index boundary estimate have passed Lean.
\end{proof}

\begin{corollary}[Upper bounds from the remaining certificates]\label{cor:reference-potential-bounds}
Use either the completed floors, or the conditional floors under their five
local share premises. Assume every local system in the exact reference union
is refuted. Suppose the chosen graph weights admit a potential with
$0\le\pi\le R$ and
\[
p+\pi(v)\le w(e)+\pi(u)
\quad\text{for every full-key edge }e:u\to v.
\]
For $m\ge9$ the corresponding snake satisfies
\[
(4200+p)m\le1098960+8p+R.
\]
With the completed floors, $(p,R)=(483,551)$ implies $m\le235$.
With the conditional floors and their five local share premises,
$(p,R)=(496,602)$ implies $m\le234$.
\end{corollary}
\begin{proof}
Proposition~\ref{prop:defined-graph-walk} gives the full-key walk. Sum its
$m-8$ potential inequalities. Intermediate potentials cancel, leaving
$p(m-8)\le W+R$. Combining this with
Theorem~\ref{thm:actual-weight-budget} proves the displayed inequality. The
two substitutions give
\[
4683m\le1103375<4683\cdot236,
\qquad
4696m\le1103530<4696\cdot235.
\]
Integrality gives the conclusions. Paths with fewer than nine edges satisfy
both bounds directly. The complete implications have passed Lean with the
exact reference-union and full-graph potential premises explicit
~\cite{referenceunionarchive}.
\end{proof}

The two concrete potential ranges are checked. Independent exact-integer
enumeration verifies both edge inequalities on all 4947008 accepted keys,
and finds no extra or missing key relative to the saved graph. The full
Lean edge certificate is still being assembled. The checked assembly rule
requires a certificate for each of the 791 assigned contexts; omitted
contexts are justified separately by their empty acceptance sets. Partial
context checks do not discharge that requirement~\cite{potentialcertificatearchive}.
Thus graph coverage and weight interpretation are complete under their
stated premises, while the reference refutations and full potential
certificate remain unresolved.''')

replace('For each saved weighted graph, a potential is checked on every transition and\nan explicit cycle attains the minimum mean.',
        'For each saved weighted graph, an exact-integer calculation checks the\npotential on every transition and an explicit cycle attains the minimum mean.')
replace('All nine target floors & $496$ & $600$ & $137941/587$\\\\',
        'Original target floors, with $012034=20$ & $496$ & $600$ & $137941/587$\\\\\nReduced targets, with $012034=18$ & $496$ & $602$ & $551765/2348$\\\\')
replace('local share theorems and gives integer bound 235, conditional on the remaining\ngraph interpretation and potential replay. The third adds one unproved local\nshare premise and still gives 235. The fourth gives 234 and retains five local\nshare premises.',
        'local share theorems and gives integer bound 235, subject to the reference\nrefutations and complete potential certificate. The third adds one unproved\nlocal share premise and still gives 235. The fourth and fifth give 234 and\nretain five local share premises. The last row reduces the $012034$ target\nwhile preserving a strict margin of 30 at length 235.')
replace('For the full target catalogue, Corollary~\\ref{cor:potential234} gives',
        'For the original full target catalogue with $012034=20$, Corollary~\\ref{cor:potential234} gives')
replace('The concrete witness and\npotential tables have not been fully embedded in Lean; the checked numerical\napplications retain their cycle and path premises. In particular, acceptance\nof these witnesses does not establish potential feasibility on every row of\nthe graph in Section~\\ref{sec:defined-graph}.',
        'The concrete witnesses retain their independent computational checks;\nthe general Lean applications retain the cycle and path premises. The\ncompleted-floor potential is now represented in Lean and its range is\nchecked, while its full edge certificate remains pending. The additional\n$012034=20$ comparisons retain their earlier numerical evidence. None of\nthese three range-optimality certificates proves that 602 is the least\nrange for the newer $012034=18$ profile.')

marker=r'\subsection{A short-walk obstruction to weakening the catalogue}'
insert=r'''\subsection{Least sufficient pending floors in the fixed model}\label{sec:least-floors}
The preceding comparison with $012034=20$ asks for more than the present
234 argument needs. Keep the graph, its other credits and the boundary
inequality fixed. Allow only the five unfinished floors to decrease to
nonnegative integers within their original target limits.

\begin{proposition}[Integer floors sufficient for the current comparison]\label{prop:least-floors}
In the order $012032,012034,012301,012340,012345$, the vectors in the box
$[0,16]\times[0,20]\times[0,16]^3$ that admit the potential criterion
\eqref{eq:strict234} on the saved graph are exactly
\[
(16,h,16,16,16),\qquad h\in\{18,19,20\}.
\]
This statement concerns integer floors and the fixed finite graph and
boundary estimate. It asserts no universal local-share bound.
\end{proposition}
\begin{proof}[Finite certificates and comparison]
For $(16,18,16,16,16)$, exact integer verification gives
\[
496+\pi(v)\le w(e)+\pi(u),\qquad 0\le\pi\le602
\]
on all 4947008 graph edges. The strict margin is
$227\cdot496-111960-602=30>0$. Increasing any floor can only increase each
weight, because the floor enters a maximum. The same potential therefore
suffices for $h=19,20$.

For necessity, weaken one floor as shown and keep the others at their
original target values. Each resulting graph retains a cycle of mean 496
and has the indicated open walk.
\begin{center}\small
\begin{tabular}{c r r r r}
\toprule
Shape & Floor & Walk length $k$ & Weight $C$ & $496k-C$\\\midrule
$012032$ & 15 & 69 & 33592 & 632\\
$012034$ & 17 & 51 & 24663 & 633\\
$012301$ & 15 & 94 & 45992 & 632\\
$012340$ & 15 & 77 & 37560 & 632\\
$012345$ & 15 & 36 & 17224 & 632\\\bottomrule
\end{tabular}
\end{center}
For any admissible slope $\mu$ and range $R$, cycle summation gives
$\mu\le496$, and the walk gives $k\mu-C\le R$. Since $k\le227$,
\[
227\mu-R\le(227-k)496+C\le111960.
\]
Thus the strict criterion fails for each row, regardless of the potential.
Every integer vector outside the asserted list lies componentwise below
one of these failed profiles. A potential valid for smaller weights would
also be valid for that profile, which is impossible. This covers simultaneous
reductions without a separate test for every vector.

The full edge calculation and all five cycle/walk witnesses have independent
exact-integer checks. The general obstruction, arithmetic and monotonicity
arguments have passed Lean; their concrete finite certificates retain the
computational evidence just described~\cite{weightintegrationarchive}.
\end{proof}

The useful local target for $012034$ is consequently share at least 18,
requiring exclusion of share at most 17. That local theorem remains open.
Range 602 is sufficient; its optimality has not been established. In
particular, the earlier seven-edge path still has weight 2872 at floor 18
and deficit 600, so it supplies no lower bound of 602 on the range. Changed
graph restrictions, boundary estimates or credits outside the stated box
can change the conclusion.

'''
replace(marker,insert+marker)
replace('This conclusion does not establish that each numerical floor is least possible: reductions by one were not tested.',
        'These earlier coarse weakenings alone do not determine the least sufficient floors. The one-unit and $18/17$ tests in Section~\\ref{sec:least-floors} provide that sharper conclusion within the specified integer box.')

# Keep ordinary notation where it is needed, without two unnecessary named definitions.
replace('The next definition separates the size of a proposed charge from the cycles\non which it contributes.',
        'An added charge can improve the minimum mean only if it affects every\ncycle that currently attains the minimum.')
replace(r'\begin{definition}[Critical cycles and the zero-bonus subgraph]\label{def:zero-bonus}',r'\label{def:zero-bonus}')
replace('G_B^0=\\bigl(V(G),\\{e\\in E(G):B(e)=0\\}\\bigr).\n\\]\n\\end{definition}',
        'G_B^0=\\bigl(V(G),\\{e\\in E(G):B(e)=0\\}\\bigr).\n\\]')
replace('\\begin{definition}\nA snake $P=(v_0,\\ldots,v_L)$ is blocked at its right endpoint when every neighbor $w$ of $v_L$ either equals a vertex $v_i$ with $i<L$, or is adjacent to such a vertex.\n\\end{definition}',
        'A snake $P=(v_0,\\ldots,v_L)$ is blocked at its right endpoint when every neighbor $w$ of $v_L$ either equals a vertex $v_i$ with $i<L$, or is adjacent to such a vertex.')

between(r'\section{Remaining requirements for a stronger bound}',r'\subsection{Sufficient charge inequalities}',r'''\section{Remaining requirements for a stronger bound}\label{sec:closure}
The maintained interval is $191\le a(9)\le235$. The newer argument has
completed its graph-coverage and weight-interpretation steps. Its remaining
requirements are:
\begin{enumerate}
\item Supply refutations for every local system in the exact union of 1378
reference keys. The checked retention theorem and bound assembly use that
union directly; reconstruction of two larger catalogue propositions is
unnecessary. An exact source selection identifies the required entries.
It does not prove their refutations.
\item Complete the finite potential certificate on all 791 assigned
direction/history contexts, for both floor choices, and check the final
assembly. The full-key walk, total charge and telescoping implications
are already checked. Exact-integer scans of all 4947008 accepted keys and
the checked potential ranges support this task; partial Lean coverage
does not replace its universal edge premise.
\item For 234, additionally prove the five local shares
$(16,18,16,16,16)$ for $012032,012034,012301,012340,012345$, including
their geometric interpretation and reversal. The completed profile needs
none of these additional share assumptions and currently recovers 235.
\end{enumerate}

Corollary~\ref{cor:reference-potential-bounds} states exactly how these
requirements imply the two numerical bounds. The reference and potential
tasks serve both arguments. The reduced $012034$ target avoids proving a
stronger share than this comparison needs. It remains a mathematical
obligation, irrespective of any earlier unsuccessful proof attempt.

Proposition~\ref{prop:least-floors} identifies the limits of further reducing
these five floors within the current integer box. Proposition~\ref{prop:joint-potential-optimality}
settles the slope/range tradeoff for three specified earlier profiles;
it does not settle the best range at the reduced floor 18. The unsaturated
cycle rules out improvements confined to count symbol six. Stronger
geometric restrictions, improved boundary accounting or information about
actual initial and final states can change these hypotheses.

The contributor's separate seven-centre count-only proposal also targets 234.
Its inspected production record retains unfinished local certificates and
transition checks~\cite{conditional234archive}. It is distinct from the present
five-centre share argument and supplies no stronger main theorem here.''')

between(r'\section{Verification scope and remaining problem}',r'\appendix',r'''\section{Verification scope and remaining problem}\label{sec:verification}
The global conclusion remains $191\le a(9)\le235$. The lower bound follows
from the explicit witness. The upper bound uses the square identity,
endpoint estimates, 1287 catalogue keys, a finite potential and path
summation. The completed contributor theorem has a successful archived
dependency audit~\cite{bound235archive}. Its final source and saved audit were
reviewed and its potential independently reconstructed. A complete
independent rebuild remains pending.

For the newer share argument, every actual window has a consistent full
direction/history/count key. All finite coverage classes and their assembly
are checked. Every local weight component, including all 55 history rules
and all compatible words, bounds the same five actual shares. The maximum,
boundary estimate and total-weight budget are connected to arbitrary snakes.
The exact-union assumption suffices to place their full-key sequence in the
graph. These implications have passed Lean under the stated remaining
reference and, for the conditional profile, local-share premises.

The concrete potential ranges are checked. Independent exact-integer scans
verify the two potential inequalities on every accepted graph key. The
complete Lean edge-certificate batch remains unfinished. Its general
assembly theorem and individual context receipts give partial progress;
only completion of all required contexts and the final assembly can
discharge the universal edge premise. The 1378 reference refutations also
remain to be supplied in the current checking environment.

The reduced five-floor target gives a strict margin of 30 at length 235.
Its local share claims remain unproved. Earlier evidence for the stronger
$012034$ target 20 supplies no proof of share 18 unless its contradiction
and interpretation chain is completed. Finite cycles and open walks prove
the stated limitations of the fixed comparison graphs, without asserting
their realizability by complete snakes.

No construction above 191 or matching optimality theorem has been obtained.
The conjecture 196 remains a numerical extrapolation and is used in none
of the proved bounds. Section~\ref{sec:closure} gives the precise remaining
requirements for the current 234 argument and the changes that could
strengthen it further.''')

replace(r'\end{thebibliography}',r'''\bibitem{weightintegrationarchive}
I.~Hironaka, T.~Ma, and S.~Zhan. \emph{Complete graph coverage, actual weights and least pending share floors}. Research milestones 97--98, included in pinned revision \texttt{00431bd4}, 3 November 2026.
\url{https://github.com/hironaka-iori/Snake-in-the-box-in-9/tree/00431bd45d7fbdaab794fb09d716e2d819ef7dbe/milestones/98-concrete-weight-integration}.

\bibitem{potentialcertificatearchive}
I.~Hironaka, T.~Ma, and S.~Zhan. \emph{Concrete potentials, context checks and the complete-certificate batch}. Research milestones 99--104, included in pinned revision \texttt{00431bd4}, 3 November 2026. The complete finite edge certificates remain pending.
\url{https://github.com/hironaka-iori/Snake-in-the-box-in-9/tree/00431bd45d7fbdaab794fb09d716e2d819ef7dbe/milestones/104-complete-potential-batch}.

\bibitem{referenceunionarchive}
I.~Hironaka, T.~Ma, and S.~Zhan. \emph{Upper-bound implications from the exact reference union}. Research milestone 105, pinned revision \texttt{00431bd4}, 3 November 2026. The checked implications retain the reference refutations and complete graph certificate as hypotheses.
\url{https://github.com/hironaka-iori/Snake-in-the-box-in-9/tree/00431bd45d7fbdaab794fb09d716e2d819ef7dbe/milestones/105-reference-proof-closure}.

\end{thebibliography}''')

assert s.split(r'\begin{abstract}')[0]==old.split(r'\begin{abstract}')[0]
assert s.count(r'\begin{definition}')==1
assert '.lean' not in s
new=s.replace('\n','\r\n').encode('utf-8')
current=EDITOR.read_bytes();assert current==MIRROR.read_bytes()
if current!=raw:
    previous=json.loads((HERE/'data/revision.json').read_text())
    assert sha(current)==previous['paper_sha256'],'Preserve unrecorded editor changes'
EDITOR.write_bytes(new);MIRROR.write_bytes(new)
record=dict(status='SAVED_PAPER106_SOURCE',previous_paper_sha256=sha(raw),paper_sha256=sha(new),
    prior_named_definitions=3,current_named_definitions=1,new_definitions=0,
    changed_prior_statement_labels=['prop:reference-union-retention','prop:defined-graph-walk'],
    removed_definition_environments=['def:zero-bonus','unlabelled_endpoint_blocking'],
    added_statement_labels=['thm:actual-weight-budget','cor:reference-potential-bounds','prop:least-floors'],
    scope='Full manuscript revision through milestone105. Graph coverage and weight chain updated; pending floor18 and exact reference assumptions stated. Existing appendices and metadata preserved.')
(HERE/'data/revision.json').write_text(json.dumps(record,indent=2)+'\n',encoding='utf-8')
print(json.dumps(record,indent=2))
