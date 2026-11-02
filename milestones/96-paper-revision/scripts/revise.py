"""Integrate milestones87--95 into the existing paper, preserving prior results."""
from pathlib import Path
import hashlib,json,zipfile

HERE=Path(__file__).resolve().parents[1];ROOT=HERE.parents[1]
EDITOR=Path('D:/Codex/2026-10-13/new-chat/outputs/snake9_research.tex');PAPER=ROOT/'paper/snake9_research.tex'
sha=lambda b:hashlib.sha256(b).hexdigest()
with zipfile.ZipFile(HERE/'data/paper-before.zip') as z:raw=z.read('snake9_research.tex')
assert sha(raw)=='eb9d5581336060b799e93b7532f59cdb485ce7f5ee39b28bd2f0fdfba4a09ec3'
current=EDITOR.read_bytes();assert current==PAPER.read_bytes()
if current!=raw:
    prior=json.loads((HERE/'data/revision.json').read_text())
    assert sha(current)==prior['paper_sha256'],'Unrecorded editor changes must be preserved'
assert raw.count(b'\r\n')==raw.count(b'\n')
old=raw.decode('utf-8').replace('\r\n','\n');s=old
def replace(a,b):
    global s
    assert s.count(a)==1,(s.count(a),a[:100])
    s=s.replace(a,b)
def between(a,b,new):
    global s
    first=s.index(a);last=s.index(b,first)
    s=s[:first]+new+'\n\n'+s[last:]

abstract=r'''\begin{abstract}
Let $a(9)$ be the maximum edge length of an induced path in the nine-dimensional binary hypercube. An explicit construction and an archived contributor proof give $191\le a(9)\le235$. We present the square census and local-count argument yielding $39m+2s_0\le9200$, where $s_0$ counts empty coordinate squares. Integer shares retain this term in local estimates. We classify all compatible eleven-direction words for 55 remembered-window share rules: 41 rules have one word and 14 have two. All 69 geometric bounds and eight stronger count-conditioned bounds are supplied, and their maximum bounds the same five-centre share sum for every fitting snake window. The actual direction, history and count sequence gives a walk in a graph defined from accepted keys, subject to explicit finite-coverage and reference-catalogue premises. The completed-local-share comparison has mean 483 and range 551; the full target comparison has mean 496 and range 600 and would imply 234. A cycle and a tight open path prove that three current comparisons are optimal jointly in constant slope and global potential range on their fixed weighted graphs. Further improvement therefore requires stronger local information, a changed graph, or stronger boundary accounting. Five target share bounds and the remaining global proof obligations are unresolved. No construction above 191 or proof of the numerical conjecture 196 is obtained.
\end{abstract}'''
between(r'\begin{abstract}',r'\clearpage',abstract)
replace('Section~\\ref{sec:current-model} defines the current finite model, compares completed and pending local evidence, constructs the actual state sequence, proves the stated filter implications, and explains the short-walk and unsaturated-cycle obstructions.',
        'Section~\\ref{sec:current-model} constructs the actual state sequence, proves the completed filter and history-credit implications, and states the remaining graph-coverage premises. It then compares the finite weighted graphs and proves the limits of changing their slope and potential range.')
replace(r'Graph interfaces and obstructions & Checked state sequence and filter implications; exact finite cycles constrain further bonuses.\\',
        r'History credits and graph interfaces & All 55 history-share rules are justified; finite graph coverage and the global potential retain explicit obligations.\\')
replace('Exact retained-transition membership and the interpretation of every credited share remain separate obligations~\\cite{currentarchive,interfacearchive}.',
        'The 55 remembered-window share rules now have complete geometric interpretation. Finite coverage of the accepted-key graph and the remaining weight components are addressed separately below~\\cite{currentarchive,interfacearchive,historycreditarchive}.')
replace('For each recognized signature, the share assigned is the minimum of the certified bounds over all compatible words. Every compatible word must be covered.',
        'A bound assigned to a recognized signature must hold for every compatible word. Proposition~\\ref{prop:history-share-classification} gives the complete lists, and Theorem~\\ref{thm:history-share-complete} supplies every bound used by the 55 share rules.')
replace('For $012034$, clause interpretation has passed and contradiction replay is in progress; its target remains unproved~\\cite{shareclosurearchive,targetsharearchive}.',
        'For $012034$, clause interpretation has passed, while the contradiction replay and target share theorem remain incomplete~\\cite{shareclosurearchive,targetsharearchive}.')

history=r'''\subsection{Complete interpretation of the remembered share rules}\label{sec:history-share-complete}
The overlap signature $\mathcal S(w)$ records the three canonical nine-direction
slices of an eleven-direction word $w$. Appendix~\ref{app:history-share-table}
lists the compatible words and bounds for every one of the 55 share signatures.
Each row is one signature; when two words occur in a row, their three canonical
slices agree. Their actual coordinate labels need not agree before normalization.

\begin{proposition}[Complete compatible-word classification]\label{prop:history-share-classification}
The 55 distinct share signatures have exactly the compatible canonical words
listed in Appendix~\ref{app:history-share-table}. There are 69 words in total:
41 signatures have one word and 14 have two. If transition $r$ emits a listed
signature and $r+9\le m$, then $r\ge2$ and the canonical eleven-direction word
beginning at $r-2$ belongs to its listed row.
\end{proposition}
\begin{proof}
Fix one signature. Its first entry fixes the first nine letters of a compatible
canonical eleven-direction word: first-occurrence relabelling does not change
when restricted to a prefix. The remaining two letters lie in
$\{0,\ldots,8\}$, giving 81 possibilities. Retain precisely those possibilities
that are canonical, describe an induced path, and have the prescribed second
and third canonical slices. The parity tests in Section~\ref{sec:upper-proof}
decide the induced-path condition. The resulting lists are the displayed rows.

Finite certificates check both inclusions: every possible compatible word is
listed, and every listed word meets all the conditions. They also check that
the 55 signatures are distinct and that the singleton and two-word counts
are 41 and 14. These finite statements have passed Lean. An independent
enumeration of all 11162 canonical induced eleven-direction words gives the
same lists~\cite{historycreditarchive}.

The history invariant identifies an emitted signature with the last three
actual nine-direction identifiers and excludes emission before $r=2$.
Their overlapping slices are those of the actual eleven-direction word
beginning at $r-2$. The finite classification therefore applies to that word.
\end{proof}

\begin{theorem}[Complete history-share bound]\label{thm:history-share-complete}
Suppose $r+9\le m$. Every applicable entry in
Appendix~\ref{app:history-share-table}, recognized by its overlap signature,
is a lower bound for
\[
\sum_{j=4}^{8}\sigma_{12}(x_{r+j}).
\]
The stronger entry in a row applies only when all its listed count caps hold.
The maximum of all applicable entries and zero is bounded by the same sum.
These conclusions require no additional geometric hypothesis on the snake.
\end{theorem}
\begin{proof}
For an emitted signature, put $s=r-2$. The preceding proposition places the
actual canonical eleven-direction word in its displayed row. The local
inequalities for every word in that row have been checked using the
forced-absence, neighbour-choice and count-saturation arguments of
Section~\ref{sec:forced-charge}. This supplies 69 geometric bounds and eight
stronger bounds with count caps. The first eight rows each have a unique
compatible word. Every row with two words has a separate geometric proof
for each word; a representative alone is never used to cover both.

Translation and coordinate permutation preserve inducedness, singleton
counts and integer shares. A local theorem charging offsets $6,\ldots,10$
from $s$ therefore charges exactly offsets $4,\ldots,8$ from $r$.
For the word $01234032563$, its geometric bound 6 comes from the canonical
final nine directions, $012310451$, beginning at $s+2$. That theorem charges
offsets $4,\ldots,8$ from $s+2$, hence the same five centres. Its stronger
bound 12 uses the full eleven-direction word and the displayed cap.

A cap on six-count position $k$ concerns $\alpha_{r+k+3}=
\alpha_{s+k+5}$. Every displayed cap is strictly below six. Therefore its
test on the truncated symbol implies the identical cap on the actual count.
The other internal positions retain the universal upper bound 21. The
coordinate transfers, cap transfers, all individual bounds and their full
combination have passed Lean in one compatible proof environment
~\cite{historycreditarchive}.

Every applicable bound concerns the same nonnegative sum, so their maximum
with zero is also bounded by that sum. When no signature is emitted, the
contribution is zero. This also covers $r=0,1$. No addition of overlapping
alternative credits is used.
\end{proof}

This theorem supplies the remembered-window component of the edge credit.
It does not identify all other credit components or verify the full graph
potential. Those are separate requirements of the global argument.

\subsection{A graph defined from accepted keys}\label{sec:defined-graph}
An edge must retain its full key: a nine-direction identifier, the preceding
history, and the six-count code. Different keys can have equal source and
target states and different weights. Independent reconstruction of the saved
graph found 4740419 distinct endpoint pairs among 4947008 rows; 206589 pairs
each have two rows. Endpoint agreement alone is therefore insufficient to
identify an edge weight~\cite{graphcoveragearchive}.

The accepted count codes are represented by a finite decision diagram that
reads six digits in $\{1,\ldots,6\}$. The 791 compatible direction/history
pairs use 127 distinct accepted-code sets. The graph considered here contains
every bounded full key accepted by its assigned diagram root, with both
endpoints computed from that key. This specifies the graph directly, without
assuming equality to an external edge array.

\begin{proposition}[Conditional coverage of actual state walks]\label{prop:defined-graph-walk}
Assume $\mathsf C_{235}$ and $\mathsf C_{236}$. Suppose that, for every
compatible direction/history pair, each six-count code passing the stated
numeric exclusion tests is accepted by its assigned diagram root. Then every
$m$-edge snake with $m\ge9$ gives a walk of $m-8$ edges in the graph just
described. Its successive vertices are the actual states of
Proposition~\ref{prop:actual-state-sequence}.
\end{proposition}
\begin{proof}
The actual candidate key at each fitting window has bounded direction,
history and count indices. Propositions~\ref{prop:local-filter-retention},
\ref{prop:history-exclusion-retention} and
\ref{prop:reference-union-retention} show that it passes the numeric tests.
The finite-coverage premise therefore places the full key among the
diagram-accepted keys. Exhaustive enumeration of those keys includes its
row. The row's endpoints are computed from the same direction slices,
history update and count shift used in the actual state sequence, so they
are the actual source and target states. Consecutive rows share their
intermediate state. There are $m-8$ fitting windows.
\end{proof}

The finite-coverage premise can be established by partitioning the six-count
domain. Each part is either accepted by the diagram or contained in a product
of six integer intervals whose vectors all trigger a proved exclusion.
The latter alternative cannot contain a code passing the numeric tests.
Shared interval products permit one geometric partition to serve several
contexts, while each context still needs its own justified exclusions.
The general partition argument and context transfer have passed Lean.
The assignment of all $505\cdot75=37875$ bounded direction/history pairs,
including the three history-dependent overrides, is also checked. The
complete family of concrete partition and exclusion certificates remains
an explicit premise until its final assembly is checked
~\cite{graphcoveragearchive}.

The walk and endpoint statements are checked under the displayed premises.
Their endpoint formulation alone does not identify the chosen row's
key-dependent credit. A complete weight argument must retain that full key
and apply Theorem~\ref{thm:history-share-complete} together with the other
credit components. The potential must be checked on every edge of this
defined graph, including any additional edges admitted by a conservative
coverage certificate. A potential verified on the saved array does not
transfer merely because the diagram was constructed from that array.
'''
between('These results connect the stated filters to arbitrary snakes.',r'\subsection{Completed local bounds and conditional comparisons}',history)

optimality=r'''\subsection{Joint limits of changing the slope and potential range}\label{sec:joint-optimality}
The comparison in~\eqref{eq:improved-potential} depends on both the constant
slope and the global range of the potential. A smaller slope might permit
a smaller range. The following proposition rules out an improvement from
that tradeoff for each of the three current weighted graphs.

\begin{proposition}[Joint optimality for a fixed weighted graph]\label{prop:joint-potential-optimality}
Let a finite directed graph have rational edge weights. Suppose a potential
satisfies
\[
M+\pi(v)\le w(u,v)+\pi(u)
\]
on every edge and has range at most $R$, where $4200+M>0$. Suppose the graph
contains a nonempty cycle of mean $M$ and an open walk of $k$ edges and total
weight $C$, with
\[
R=kM-C,\qquad
k+8\le\frac{1098960+8M+R}{4200+M}.
\]
For any other rational slope $\mu$ and potential with range at most $\rho$
satisfying the same edge inequalities, with $4200+\mu>0$,
\[
\frac{1098960+8\mu+\rho}{4200+\mu}
\ge\frac{1098960+8M+R}{4200+M}.
\]
Thus changing only the slope and global range cannot sharpen this comparison.
\end{proposition}
\begin{proof}
Summing the competing inequalities around the cycle gives $\mu\le M$.
Summing along the open walk gives $k\mu-C\le\rho$. Write $B_*$ for the
right-hand comparison fraction in the conclusion. Since $R=kM-C$,
\[
\begin{aligned}
1098960+8\mu+\rho-B_*(4200+\mu)
&\ge1098960-C+(k+8)\mu-B_*(4200+\mu)\\
&=(k+8-B_*)(\mu-M)\ge0.
\end{aligned}
\]
Both factors in the last product are nonpositive. Division by
$4200+\mu>0$ proves the assertion. The baseline potential attains the
displayed comparison. Path telescoping, the cycle slope bound and this
rational comparison have passed Lean~\cite{potentialcomparisonarchive}.
\end{proof}

The three current certificates have the following open-walk data. The means
and ranges use the unscaled weight units of the preceding comparison table.
\begin{center}\small
\begin{tabular}{l r r r r}
\toprule
Profile & $M$ & $k$ & $C$ & $R=kM-C$\\\midrule
Completed local floors & $483$ & 9 & 3796 & $551$\\
Additional proposed $012034$ floor & $9259/19$ & 31 & 14512 & $11301/19$\\
Full target floors & $496$ & 7 & 2872 & $600$\\
\bottomrule
\end{tabular}
\end{center}
Their cycles have lengths 4, 19 and 3 and total weights 1932, 9259 and 1488.
The short-walk hypothesis is equivalent to
$1098960-C-4200(k+8)\ge0$; its values are respectively 1023764, 920648 and
1033088. All three comparisons are therefore optimal under the proposition's
fixed-graph, fixed-weight and fixed-boundary hypotheses. Their best integer
comparisons remain 235, 235 and 234.

Exact integer calculations verify all 4947008 potential inequalities for
each pinned array graph. Independent checks verify the cycle and open-walk
keys, endpoints, weights and potential differences. The paths run from a
maximum potential value to a minimum along tight edges. The witness keys
are also accepted by the saved decision diagram. The concrete witness and
potential tables have not been fully embedded in Lean; the checked numerical
applications retain their cycle and path premises. In particular, acceptance
of these witnesses does not establish potential feasibility on every row of
the graph in Section~\ref{sec:defined-graph}.

This result directs further optimisation toward stronger local inequalities,
additional restrictions valid for actual snakes, a stronger boundary sum,
or a potential estimate depending on the actual initial and final states.
It places no restriction on such changes to the argument.
'''
replace(r'\subsection{A short-walk obstruction to weakening the catalogue}',optimality+'\n'+r'\subsection{A short-walk obstruction to weakening the catalogue}')

closure=r'''\section{Remaining requirements for a stronger bound}\label{sec:closure}
The maintained interval is $191\le a(9)\le235$. Corollary~\ref{cor:eighteen-empty}
shows that eighteen empty squares would exclude a hypothetical 235-edge snake.
The target charge graph meets a sufficient numerical criterion for that
exclusion. Its remaining proof obligations are now more specific.
\begin{enumerate}
\item Complete the five count-independent targets for $012032$, $012034$,
$012301$, $012340$ and $012345$, including geometric interpretation and
reversal. The four completed target floors and the weaker distinct-direction
floor 12 remain available independently.
\item Supply the two closed reference-catalogue proofs in the current checking
environment and complete the finite diagram-coverage certificates. The actual
state sequence, ten interval filters, forty short filters, three history
exclusions and complete context assignment are checked. Under the remaining
premises, Proposition~\ref{prop:defined-graph-walk} supplies an actual state walk.
\item Preserve each selected edge's full key and justify the maximum of all
credit components for that key. The 55 history-share rules, all their
compatible words and their maximum are completed in
Theorem~\ref{thm:history-share-complete}. The other share components and their
combination still need to be connected to the same five actual centres.
\item Check the entire potential and its range on the defined graph in Lean,
telescope along the actual walk, and apply Proposition~\ref{prop:boundary21}.
The integer check of all 4947008 saved array edges supplies finite-model
evidence; it does not complete this arbitrary-snake dependency chain.
\end{enumerate}

Proposition~\ref{prop:joint-potential-optimality} shows that reoptimising only
the slope and global potential range cannot improve the three fixed
comparisons. The short-walk obstruction covers six specified weakenings of
the target catalogue. The unsaturated-cycle obstruction excludes improvements
based solely on additional charge at count symbol six. Stronger geometric
restrictions, improved boundary accounting or information about actual initial
and final states can change these hypotheses and remain possible routes.

The contributor's separate seven-centre count-only proposal also targets 234.
Its inspected production record retains unfinished local certificates and
transition checks~\cite{conditional234archive}. It is distinct from the present
five-centre share model and is not used to strengthen the main theorem.
'''
between(r'\section{Remaining requirements for a stronger bound}\label{sec:closure}',r'\subsection{Sufficient charge inequalities}',closure)

verification=r'''\section{Verification scope and remaining problem}\label{sec:verification}
The global conclusion remains $191\le a(9)\le235$. The lower bound follows
from the explicit witness. The upper bound uses the square identity, endpoint
estimates, 1287 catalogue keys, a finite potential and the path summation.
The completed contributor theorem has a successful archived dependency audit
~\cite{bound235archive}; its assumptions were discharged in that development.
The final source and saved audit were reviewed and the potential independently
reconstructed. A complete independent rebuild remains pending.

The count-independent share theorem covers five shapes, four meeting the
stronger nine-shape target. Five target floors remain incomplete. The
$012034$ contradiction replay has no completed final audit and contributes
no new unconditional share theorem. The weaker bound for six distinct
directions does not prove its stronger target.

The 55 history-share signatures now have exact compatible sets and complete
local bounds. All 69 geometric inequalities and eight stronger capped
inequalities are connected to actual windows; their maximum bounds the same
five-centre share sum. The coordinate, cap and suffix transfers and the full
combination have passed Lean. These results coexist with the checked graph
interfaces. They do not discharge the other weight components or the global
potential.

The actual direction, history and count sequence passes the completed filters.
The reference retention theorem retains two catalogue premises. The complete
finite context assignment is checked, and the diagram-defined graph contains
the actual state walk under the remaining coverage premise. Individual
coverage certificates do not establish that entire premise until all required
classes are assembled. Endpoint equality alone also does not identify a
key-dependent weight when parallel rows have the same endpoints.

For the pinned finite array graphs, exact potential checks and attaining
cycles give the stated means. Tight open paths additionally prove that the
three current slope/range comparisons are jointly optimal. The general
rational arguments are Lean-checked; concrete graph witnesses and full
potential tables retain their separate computational evidence. The full
target comparison meets the 234 criterion with margin 32 at length 235,
subject to the remaining local and global assumptions.

No construction above 191 or matching optimality theorem has been obtained.
The conjecture 196 is an extrapolation and enters none of the proved bounds.
Section~\ref{sec:closure} states the remaining conditions for 234 and the
changes that could strengthen the argument further. Complete snakes establish
the stated sharpness examples; local forests and abstract graph cycles do
not supply additional snake constructions.
'''
between(r'\section{Verification scope and remaining problem}\label{sec:verification}',r'\appendix',verification)

data_path=ROOT/'milestones/94-history-share-dispatch/data/variants.json'
rows=json.loads(data_path.read_text())['rows']
table=r'''\section{Complete history-share catalogue}\label{app:history-share-table}
Each row below represents one overlap signature $\mathcal S(w)$. The listed
words are all its compatible canonical eleven-direction words. A word begins
at $x_s$ and the bounds concern $\sum_{j=6}^{10}\sigma_{12}(x_{s+j})$.
The geometric bound has no count hypothesis. A stronger bound applies under
all listed caps; a dash means that no additional capped bound is needed.
For a signature emitted at transition $r$, one has $s=r-2$. All caps are below
six, so testing them on truncated counts gives the same actual-count caps.

\begingroup\small
\begin{longtable}{r p{0.28\textwidth} p{0.33\textwidth} r r}
\caption{All compatible words and credits for the 55 history-share rules.}\label{tab:history-share-catalogue}\\
\toprule
Row & Canonical words & Additional caps & Geometric & Stronger\\\midrule
\endfirsthead
\toprule
Row & Canonical words & Additional caps & Geometric & Stronger\\\midrule
\endhead
\bottomrule\endfoot
'''
for i,row in enumerate(rows):
    words=r'\newline '.join(r'\(\mathtt{'+''.join(map(str,w))+r'}\)' for w in row['variants'])
    caps=r'\newline '.join(r'\(\alpha_{s+'+str(int(k)+5)+r'}\le'+str(v)+r'\)' for k,v in sorted(row['caps'].items(),key=lambda x:int(x[0]))) or 'None'
    strong=str(row['lower']) if row['caps'] else '--'
    table+=f"{i+1} & {words} & {caps} & {row['geometric_lower']} & {strong}"+r'\\'+'\n'
table+=r'''\end{longtable}
\endgroup
The finite classification and every displayed local bound are checked in
the archived proof collection~\cite{historycreditarchive}. In particular,
both words in every two-word row support its geometric bound. This table
supplies local inequalities, not a claim that its rows can be concatenated
into a globally realizable snake.

'''
reference_marker=r'\clearpage'+'\n'+r'\addcontentsline{toc}{section}{References}'
replace(reference_marker,table+reference_marker)
refs=r'''\bibitem{graphcoveragearchive}
I.~Hironaka, T.~Ma, and S.~Zhan. \emph{Accepted-key graphs, finite coverage and context assignment}. Research milestones 87--92, included in pinned revision \texttt{32445d35}, 3 November 2026.
\url{https://github.com/hironaka-iori/Snake-in-the-box-in-9/tree/32445d353f0a8527a2732eff404f1c86d00092ff/milestones}.

\bibitem{potentialcomparisonarchive}
I.~Hironaka, T.~Ma, and S.~Zhan. \emph{Joint slope and potential-range comparisons on fixed graphs}. Research milestone 93, pinned revision \texttt{f4b28638}, 3 November 2026.
\url{https://github.com/hironaka-iori/Snake-in-the-box-in-9/tree/f4b2863825689bb9d7c2c056d845395ca2837481/milestones/93-defined-graph-potential}.

\bibitem{historycreditarchive}
I.~Hironaka, T.~Ma, and S.~Zhan. \emph{Complete compatible-word classification and concrete history-share bounds}. Research milestones 94--95, pinned revision \texttt{32445d35}, 3 November 2026.
\url{https://github.com/hironaka-iori/Snake-in-the-box-in-9/tree/32445d353f0a8527a2732eff404f1c86d00092ff/milestones}.

'''
replace(r'\end{thebibliography}',refs+r'\end{thebibliography}')

new=s.replace('\n','\r\n').encode('utf-8')
assert new.split(b'\\begin{abstract}')[0]==raw.split(b'\\begin{abstract}')[0]
old_appendix=old.split(r'\appendix',1)[1].split(reference_marker,1)[0]
new_appendix=s.split(r'\appendix',1)[1].split(r'\section{Complete history-share catalogue}',1)[0]
assert old_appendix==new_appendix
EDITOR.write_bytes(new);PAPER.write_bytes(new)
record=dict(status='PAPER96_REVISED_AWAITING_SOURCE_AND_COMPILER_CHECKS',previous_sha256=sha(raw),paper_sha256=sha(new),bytes=len(new),
    added_statement_labels=['prop:history-share-classification','thm:history-share-complete','prop:defined-graph-walk','prop:joint-potential-optimality'],
    changed_prior_statement_labels=[],added_named_definitions=0,metadata_preserved=True,original_appendix_body_preserved=True,
    history_table_rows=55,history_table_words=69,history_table_caps=8,history_table_input=data_path.relative_to(ROOT).as_posix(),history_table_input_sha256=sha(data_path.read_bytes()),
    script_sha256=sha(Path(__file__).read_bytes()),scope='Existing editor source revised in place and synchronized; numerical interval unchanged. Compilation and source checks remain separate.')
(HERE/'data/revision.json').write_text(json.dumps(record,indent=2)+'\n')
print('PAPER96_REVISED',len(new),sha(new))
