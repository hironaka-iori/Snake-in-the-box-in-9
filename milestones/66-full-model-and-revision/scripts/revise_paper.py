"""Integrate the completed research into the existing manuscript and editor mirror."""
from pathlib import Path
import hashlib,json,re
HERE=Path(__file__).resolve().parents[1];ROOT=HERE.parents[1]
paper=ROOT/'paper/snake9_research.tex';mirror=Path('D:/Codex/2026-10-13/new-chat/outputs/snake9_research.tex')
old=paper.read_text(encoding='utf-8');before=hashlib.sha256(paper.read_bytes()).hexdigest()
assert before=='b4db98102b7a74bc0ca41d69fe49a3bbe24ef61c974f3d88755bb5101c33e50e'
assert paper.read_bytes()==mirror.read_bytes()
s=old
def replace(a,b):
    global s
    assert s.count(a)==1,(a[:90],s.count(a));s=s.replace(a,b)
abstract=r'''Let $a(9)$ be the largest number of edges in an induced path in the nine-dimensional binary hypercube. An explicit construction and a completed contributor proof give $191\le a(9)\le235$. We present the square census and endpoint argument yielding $39m+2s_0\le9200$, where $m$ is the path length and $s_0$ counts empty coordinate squares. We then retain empty squares through integer shares. Vertices forced absent by a selected segment give share lower bounds; exhaustive local neighbour choices and saturation of singleton-count caps strengthen them. Three short geometric arguments each force at least three singleton squares at a specified internal vertex. These results apply to arbitrary matching snakes and have passed Lean checks. Explicit overlap and boundary accounting explains how local shares can enter a global upper bound. In the complete recorded exploratory model, the new restrictions raise the exact integer minimum from $9891/20$ to $18823/38$. An attaining cycle and an all-edge potential certify the finite computation, but inherited numerical premises and the complete graph-to-snake assembly remain unfinished. The remaining minimum-mean family has 70 states and 99 transitions. Earlier local inequalities, sharpness witnesses, and finite-model obstructions are retained with their scopes. The value 196 remains a numerical conjecture, without a matching construction or optimality proof.'''
a=s.index(r'\begin{abstract}')+len(r'\begin{abstract}');b=s.index(r'\end{abstract}',a)
s=s[:a]+'\n'+abstract+'\n'+s[b:]
start=s.index('The rest of the argument separates local geometry')
end=s.index(r'\begin{center}',start)
s=s[:start]+r'''The subsequent argument develops the empty-square term in three stages. Sections~\ref{sec:empty-packing} and~\ref{sec:forced-charge} define integer shares and prove lower bounds from absent vertices, finite alternatives, and singleton-count saturation. Section~\ref{sec:long-counts} gives direct geometric restrictions on longer segments. Sections~\ref{sec:common-budget} and~\ref{sec:long-models} account for overlapping charges and all boundary losses, then separate complete finite models from restricted critical families. The numerical conjecture and construction criteria are assessed after these deductions. Earlier finite-model obstructions and complete witness sequences remain in the appendices. In particular, an exclusion of a minimum-mean cycle is used only within its stated graph; replacement cycles are checked separately.

'''+s[end:]
replace(r'Finite-model mean $102/25$ & A cycle and an all-edge potential for the current exploratory model; some local premises remain unreplayed.',r'Local empty-square bounds & Arbitrary-snake proofs from forced absence, neighbour choices and count saturation.\\'+'\n'+r'Finite-model mean $18823/4560$ & A cycle and an all-edge potential; inherited premises and complete snake coverage remain unfinished.')
# Keep the old model and its mathematical statements, with an explicit historical referent.
a=s.index(r'\subsection{Five-window accounting and the current obstruction}')
b=s.index(r'\section{Remaining requirements for a stronger bound}',a)
historical=s[a:b]
historical=historical.replace(r'\subsection{Five-window accounting and the current obstruction}',r'\section{The earlier five-window model and its zero-credit obstruction}\label{app:earlier-five-model}')
historical=historical.replace('The current product graph uses','The earlier product graph considered in this appendix uses')
historical=historical.replace('The current exploratory graph contains a 25-step cycle','The earlier exploratory graph described in this appendix contains a 25-step cycle')
historical=historical.replace('The limitation concerns the present recorded lower bounds','The limitation concerns the lower bounds recorded in this earlier model')
historical=historical.replace('A new local inequality must assign positive credit to this surviving family','To strengthen that earlier model, a new local inequality must assign positive credit to its surviving family')
s=s[:a]+s[b:]
replace(r'\appendix',r'\appendix'+'\n'+historical)

geometry=r'''\section{Deriving empty-square bounds from local geometry}\label{sec:forced-charge}
The share definition uses the full selected set $S$, but a lower bound can often be proved from a short selected segment. The essential fact is that enlarging the selected set can only decrease the relevant share. This permits finite calculations on a superset that need not itself be a snake.

\begin{lemma}[Monotonicity under enlarging the selected set]\label{lem:share-monotonicity}
For $A\subseteq\Q_9$, let $e_A(q)$ count coordinate squares through $q$ disjoint from $A$, and let $d_A(q)=|N(q)\cap A|$. If $S\subseteq U$ and $x\in S$, then
\[
\sum_{q\sim x}\left\lfloor\frac{12e_U(q)}{d_U(q)}\right\rfloor
\le\sigma_{12}(x).
\]
\end{lemma}
\begin{proof}
Every denominator is positive because $x$ belongs to both sets. For each $q\sim x$, inclusion gives $e_U(q)\le e_S(q)$ and $d_S(q)\le d_U(q)$. Hence $e_U(q)/d_U(q)\le e_S(q)/d_S(q)$. Multiplication by 12, taking the floor, and summation preserve the inequality. The positive-denominator argument and the corresponding integer inequalities have been checked in Lean~\cite{geometricarchive}.
\end{proof}

\begin{lemma}[Degree-forced absence]\label{lem:degree-forced}
Let $A\subseteq S$ be known selected vertices. If the induced subgraph on $A\cup\{q\}$ has a vertex of degree at least three, then $q\notin S$. In particular, every neighbour outside $A$ of a vertex having two neighbours in $A$ is absent.
\end{lemma}
\begin{proof}
If $q\in S$, then $A\cup\{q\}\subseteq S$. A vertex of degree at least three in this subset would have degree at least three in the graph induced by $S$, contradicting the snake condition. This also covers the case where $q$ itself has three neighbours in $A$.
\end{proof}

Let $W=(x_r,\ldots,x_{r+n})$ be an induced segment and let $D$ be any set of vertices proved absent using this lemma. Put $U=\Q_9\setminus D$. For a set $C\subseteq W$ of five internal centres define
\begin{equation}\label{eq:absence-share}
L_D(C)=\sum_{x\in C}\sum_{q\sim x}
\left\lfloor\frac{12\,\#\{Q:q\in Q,\ Q\subseteq D\}}
{9-|N(q)\cap D|}\right\rfloor.
\end{equation}
The numerator counts coordinate squares. The denominator is positive because $x\in C\subseteq S\subseteq U$.

\begin{theorem}[Forced-absence share bound]\label{thm:forced-share}
With the preceding notation,
\[
L_D(C)\le\sum_{x\in C}\sigma_{12}(x).
\]
Increasing a justified absence set $D$ can only strengthen this lower bound. Several lower bounds on the same five-centre share may be combined by taking their maximum.
\end{theorem}
\begin{proof}
The complement $U$ contains $S$, and the expression in~\eqref{eq:absence-share} is precisely the left side of Lemma~\ref{lem:share-monotonicity}, summed over $C$. Increasing $D$ decreases $U$ and applies the same monotonicity argument. Every available bound is at most the same share sum, so their maximum is also at most that sum. Their sum would need a separate overlap argument.
\end{proof}

The construction is invariant under translations and coordinate permutations. For eight-transition segments, choose internal positions 3 through 7. Direct enumeration gives 132 direction shapes up to relabelling, 76 with positive bounds, and maximum bound 18. For nine-transition segments, choose positions 4 through 8. There are 505 shapes, 357 with positive bounds; 231 improve on the corresponding eight-transition suffix, and the maximum is 54. All positive instances and their arbitrary-snake interpretations have passed Lean. The independent calculation enumerates all 4608 coordinate squares, every denominator and every summand. The formula also defines the zero entries, so no unlisted shape is assigned a positive bound~\cite{geometricarchive}.

For longer segments, the same argument applies to any five selected centres. It supplies 20 checked ten-transition instances on an earlier attaining cycle, and 96 positive ten- or eleven-transition instances on the complete critical family discussed in Section~\ref{sec:restricted-family}. These are local inequalities for arbitrary matching segments; membership in a particular finite family is unnecessary for their validity.

\subsection{Finite alternatives and complete neighbour choices}
An absent-vertex calculation can be strengthened by branching on a vertex whose membership in $S$ is unknown. In the absent alternative, add that vertex to $D$. In the selected alternative, add it to $A$ and apply Lemma~\ref{lem:degree-forced}. A bound valid in both alternatives holds for the original segment.

\begin{proposition}[Exhaustive local choice bound]\label{prop:local-choice-share}
Suppose a finite list of alternatives covers every selected set satisfying the stated local hypotheses. In each alternative, derive either a contradiction or an absence set giving a share bound $L_t$ on the same centres $C$. If every surviving alternative has $L_t\ge L$, then $\sum_{x\in C}\sigma_{12}(x)\ge L$.
\end{proposition}
\begin{proof}
The actual selected set satisfies one of the alternatives. It cannot satisfy an alternative proved contradictory. In its surviving alternative, Theorem~\ref{thm:forced-share} gives the claimed inequality.
\end{proof}

A useful complete list is obtained from each end of a local segment. That end already has one selected neighbour in the segment and can have at most one further selected neighbour. After removing vertices already known absent, enumerate the alternatives of no further selected neighbour and each individual candidate neighbour. Enumerate these choices jointly at the two local ends. Every actual snake satisfies one joint choice. These ends are local segment ends and may be internal vertices of the full snake; no global endpoint-demand assumption is used.

Single-vertex splits give eight stronger bounds on the nine-transition critical windows and 38 on the eleven-transition windows. Complete neighbour choices give 34 further improvements on eleven-transition windows. The last calculation checks 11,554 joint configurations on 214 distinct direction shapes. The arbitrary-snake inequalities are obtained by the preceding exhaustive alternatives and degree-forcing argument. Their individual finite checks and choice coverage have passed Lean~\cite{choicearchive}.

\subsection{Saturation of a singleton-count cap}
At an internal vertex $x$, let $K$ be its 21 opposite corners from coordinate pairs avoiding the incoming and outgoing directions. Lemma~\ref{lem:window-missing-corners} gives $\alpha_S(x)=|K\setminus S|$.

\begin{proposition}[Count saturation]\label{prop:count-saturation}
Suppose $D\cap S=\varnothing$, $A\subseteq S$, and $\ell\le\alpha_S(x)\le h$. Then
\[
|K\cap(D\cup\{q\})|>h\ \Longrightarrow\ q\in S,
\]
and
\[
|K\cap(A\cup\{q\})|>21-\ell\ \Longrightarrow\ q\notin S.
\]
The inequalities $|K\cap D|>h$ or $|K\cap A|>21-\ell$ directly contradict the hypotheses.
\end{proposition}
\begin{proof}
For the first implication, if $q\notin S$, every vertex in $K\cap(D\cup\{q\})$ is an absent corner, contradicting the upper bound $h$. For the second, if $q\in S$, all vertices in $K\cap(A\cup\{q\})$ are selected. Since $|K|=21$, the number of absent corners is then smaller than $\ell$. The terminal contradictions are the same counts without $q$. These statements, their iteration with degree-forced absence, and their application to arbitrary snakes have passed Lean~\cite{choicearchive}.
\end{proof}

The deduction process alternates selected and absent facts. A count cap may force new selected corners; these selected vertices can force further absences and empty squares. Each step preserves facts true of every selected set under consideration. This justifies a finite trace ending in a share bound or contradiction.

The following nine consequences require only the indicated upper bounds. Write $A_j=\alpha_{r+j}$, and represent distinct coordinate labels by distinct digits. Every row bounds $\sum_{j=6}^{10}\sigma_{12}(x_{r+j})$. All other singleton counts are unrestricted beyond their universal bounds.
\begin{theorem}[Count-conditioned five-centre shares]\label{thm:saturated-shares}
The direction word and count caps in each row imply the stated lower bound $L$:
\begin{center}\small
\begin{tabular}{l l r}
\toprule
Eleven directions & Required upper bounds & $L$\\\midrule
@@SHARE_ROWS@@
\bottomrule
\end{tabular}
\end{center}
\end{theorem}
\begin{proof}[Computer-assisted proof]
Normalize the segment by translation and coordinate permutation. Enumerate all joint neighbour choices at its two ends. Apply degree-forced absence and Proposition~\ref{prop:count-saturation} until either a contradiction is reached or an absence mask gives the required share. There are 443 checked branches across these nine rows. Only the count caps printed in the table are used; lower count bounds and unused upper bounds have been removed. The finite branch checks, semantic interpretation of every deduction, and arbitrary-coordinate transport have passed Lean. A separate reconstruction checks the 21-corner sets and all reduced absence masks~\cite{choicearchive}.
\end{proof}

\section{Direct count restrictions on longer segments}\label{sec:long-counts}
The same geometry gives short proofs of restrictions that were first encountered during share calculations. They do not require a large local refutation.

\begin{theorem}[Three forced opposite corners]\label{thm:three-forced-corners}
For six distinct coordinates $a,b,c,d,e,f$, each direction pattern beginning at $x_r$ has the stated consequence:
\[
\begin{array}{c|c}
\text{eleven directions}&\text{singleton count}\\\hline
(a,b,c,d,a,e,d,c,f,e,d)&\alpha_{r+10}\ge3\\
(a,b,c,d,e,f,d,c,a,b,d)&\alpha_{r+8}\ge3\\
(a,b,c,d,e,f,d,c,a,f,d)&\alpha_{r+10}\ge3
\end{array}
\]
No conditions on the other singleton counts are imposed.
\end{theorem}
\begin{proof}
Translate $x_r$ to zero and assign $a,b,c,d,e,f$ to coordinates $0,1,2,3,4,5$. The canonical selected vertices, target vertex, and three absent corners are listed below. Consecutive entries are joined by the prescribed transition.
\begin{center}\small
\begin{tabular}{p{0.64\textwidth}r l}
\toprule
Selected vertices & Target & Opposite corners\\\midrule
$0,1,3,7,15,14,30,22,18,50,34,42$ & 34 & $6,33,39$\\
$0,1,3,7,15,31,63,55,51,50,48,56$ & 51 & $17,27,33$\\
$0,1,3,7,15,31,63,55,51,50,18,26$ & 18 & $6,17,23$\\
\bottomrule
\end{tabular}
\end{center}
In the first row, vertex 1 has selected neighbours 0 and 3, excluding 33. Vertex 7 has selected neighbours 3 and 15, excluding 6 and 39. In the second row, vertex 1 excludes 17 and 33, and vertex 31, with selected neighbours 15 and 63, excludes 27. In the third row, vertex 7 excludes 6 and 23, while vertex 1 excludes 17. Each exclusion is Lemma~\ref{lem:degree-forced}.

In table order, the free coordinate pairs producing these opposite corners at the target are
\[
\bigl((2,5),(0,1),(0,2)\bigr),\quad
\bigl((1,5),(3,5),(1,4)\bigr),\quad
\bigl((2,4),(0,1),(0,2)\bigr).
\]
These pairs avoid both directions incident to the target along the segment. Their corners are distinct and absent, so Lemma~\ref{lem:window-missing-corners} gives at least three singleton squares. Translation and permutation preserve all conditions. All three finite checks and the arbitrary-snake conclusions have passed Lean~\cite{choicearchive,newmodelarchive}.
\end{proof}

Ordinary induced-path validity also constrains longer direction windows. If a proposed segment selects every vertex of a finite cycle with two neighbours at each vertex, Lemma~\ref{lem:subset-low-degree} excludes it. This criterion proves 27 distinct twelve-vertex cycle exclusions in the recorded longer-window family. In particular, the words
\[
(0,1,2,3,1,0,4,1,3,2,1),\quad
(0,1,2,0,3,4,0,2,1,0,4),\quad
(0,1,2,3,4,2,1,0,2,4,3)
\]
would introduce an edge between the first and last vertices. The exclusions and their arbitrary-coordinate interpretations are checked; other direction words can replace them in a finite relaxation. These validity controls therefore support the share calculation without establishing that every low-charge cycle is impossible~\cite{geometricarchive}.

'''
rows=[]
used=json.loads((ROOT/'milestones/65-count-saturation-share/data/verification.json').read_text())['upper_premises_used']
certs=json.loads((ROOT/'milestones/65-count-saturation-share/data/compact-certificates.json').read_text())['rows']
for entry in certs:
    if entry['mode']!='share':continue
    i=entry['edge'];data=json.loads((ROOT/f'milestones/65-count-saturation-share/data/cases/e{i:03d}.json').read_text())
    word=''.join(map(str,data['directions']))
    caps=r',\ '.join('A_{'+str(k+5)+'}\\le'+str(data['constraints'][k]['hi']) for k in used[str(i)])
    rows.append(f'${word}$ & ${caps}$ & {entry["lower"]}'+r'\\')
geometry=geometry.replace('@@SHARE_ROWS@@','\n'.join(rows))
replace(r'\section{Compatibility between overlapping windows}',geometry+r'\section{Compatibility between overlapping windows}')

models=r'''\section{Longer-window accounting and complete finite models}\label{sec:long-models}
Local share inequalities must be summed with a fixed capacity for every path position. The length of the segment used to prove an inequality and the number of centres charged are separate quantities. Retaining a longer segment can strengthen the local bound while leaving the fivefold share capacity unchanged.

\begin{proposition}[Five-centre accounting with an $n$-transition context]\label{prop:general-window-budget}
Let $m\ge n\ge6$. For every start $0\le r\le m-n$, suppose $L_r$ is a valid nonnegative lower bound on the shares at the final five internal vertices of the segment $(x_r,\ldots,x_{r+n})$. Set
\[
W_n=\sum_{r=0}^{m-n}\bigl(120b_{r+n-1}+L_r\bigr).
\]
Then
\[
W_n+120(n+6)\le5G_{12},\qquad
W_n+4200m\le1100760-120n.
\]
If an integer potential of range $R$ satisfies $p+\pi(v)\le d\,w(u,v)+\pi(u)$ on every transition traced by this sequence, with $p,d>0$, then
\begin{equation}\label{eq:general-window-potential}
(p+4200d)m\le(1100760-120n)d+(n-1)p+R.
\end{equation}
\end{proposition}
\begin{proof}
The counted internal indices are $n-1,\ldots,m-1$. The omitted $n-2$ internal vertices contribute at least $n-2$ to $T$, and the two endpoints contribute at least eight. Thus
\[
\sum_{j=n-1}^{m-1}b_j+n+6\le T.
\]
Each share is counted by at most five distinct starts, so $\sum_r L_r\le5\Sigma$. Multiply the preceding count inequality by 120 and add this share inequality to obtain the first assertion. Combining it with $5G_{12}+4200(m+1)\le1105680$ gives the second. Finally, there are $m-n+1$ transitions, so telescoping gives $p(m-n+1)\le dW_n+R$. Substitution yields~\eqref{eq:general-window-potential}. The offset-independent overlap argument and the conditional arithmetic have passed Lean~\cite{geometricarchive}. A particular model still has to establish that every relevant snake traces permitted transitions.
\end{proof}

For $m<n$, the elementary bound $m<n$ suffices whenever the intended upper bound is at least $n-1$. No empty or negative number of windows is used. The earlier eight-transition accounting and its zero-credit obstruction are retained in Appendix~\ref{app:earlier-five-model}.

\subsection{The limit of reweighting a fixed local calculation}
Let $g_1,\ldots,g_5$ be the individual forced-share bounds at five centres, and let $H$ be the larger of their sum and another available total-share bound. For nonnegative coefficients $c,v_1,\ldots,v_5$ with $5c+\sum_i v_i=5$, the weighted share is at least $cH+\sum_i v_i g_i$. This follows by adding $c$ times the total bound and $v_i$ times each individual bound. The six vertices of this coefficient simplex are uniform weighting and weight five on a single centre.

On the saved twenty-transition cycle of the eight-transition model, these six choices have integer means
\[
\frac{2468}{5},\quad\frac{987}{2},\quad493,\quad
\frac{987}{2},\quad\frac{989}{2},\quad\frac{987}{2}.
\]
Their maximum is $989/2$. Linearity therefore bounds every fixed weighting in this relaxation by the same value on that cycle. Even with zero potential-range loss, setting $n=8$ in~\eqref{eq:general-window-potential} requires an integer mean greater than $9400/19>989/2$ to exclude $m=235$. The cycle coefficients were independently checked, and the convexity and boundary implications have passed Lean. This rules out that specific fixed-weight improvement; it does not constrain additional absent-vertex information or stronger count conditions.

\subsection{Complete models before the eleven-transition refinements}
The nine-transition model retains eight normalized directions and five count symbols in each state. A transition supplies nine directions and six counts, at internal positions 3 through 8. Its weight is $120b_{\mathrm{new}}+L$, where $L$ bounds the final five internal shares. Symbol six continues to represent $[6,21]$.

The following are exact minima of the recorded complete finite models. Each value is certified computationally by an integer potential on every transition and a cycle attaining equality. Some inherited exclusions and count-specific shares remain numerical premises, so these computations are separate from the global theorem.
\begin{center}\small
\begin{tabular}{p{0.48\textwidth}r r}
\toprule
Model or added information & Normalized mean & Transitions\\\midrule
Earlier candidate share refinement & $49/12$ & 3042328\\
Eight-transition forced absence & $617/150$ & 3042328\\
Nine-transition memory with old shares & $617/150$ & 11594078\\
Nine-transition forced absence & $3297/800$ & 11594078\\
Eleven-transition count restriction, tracked through history & $18823/4560$ & 11772559\\
Above with eight count-conditioned share patterns & $18823/4560$ & 12893079\\
Above with both further count restrictions & $18823/4560$ & 13173896\\
\bottomrule
\end{tabular}
\end{center}
The initial candidate refinement has unreplayed share premises. The forced-absence catalogues themselves are proved, while their inherited models retain earlier numerical rules. The complete eight-transition graph has 264384 states, and the nine-transition graph has 1026432. The changes in edge totals after adding history reflect different state spaces; they are not counts of newly allowed geometric configurations.

For the nine-transition forced-absence model, the integer mean is $9891/20$, and the potential range is 12101. Equation~\eqref{eq:general-window-potential} gives the conditional estimate
\[
m\le\frac{22084829}{93891}.
\]
Even replacing this range by zero cannot yield 234, because the required mean would exceed $112680/227$, whereas $9891/20$ is smaller. Additional geometric information is necessary under this accounting.

\subsection{Restricted families and replacement cycles}\label{sec:restricted-family}
The exact potential of the nine-transition graph identifies a minimum-mean family of 49 states and 74 transitions. Extending all its compatible contexts gives a ten-transition graph with 74 states and 121 transitions, and an eleven-transition graph with 118 states and 218 transitions. Twenty-eight extensions are rejected by 27 distinct cycle exclusions. These graphs retain only contexts coming from the selected family; they do not cover arbitrary snakes by themselves.

The progression of exact normalized means in the eleven-transition restricted graph is
\[
\frac{4961}{1200},\quad\frac{2483}{600},\quad
\frac{4973}{1200},\quad\frac{1991}{480},\quad
\frac{9961}{2400}.
\]
These values use, successively, forced absence, shorter vertex splits, eleven-transition vertex splits, complete neighbour choices, and count-conditioned shares. Each restricted potential and attaining cycle has been checked in Lean. Their larger means cannot be substituted for the mean of the complete model, because a path can leave the restricted family.

The first row of Theorem~\ref{thm:three-forced-corners} excludes a transition in this family whose terminal count is two. Every cycle in the saved 118-state graph uses that transition. After its removal, an integer rank increases by at least one on all 217 remaining transitions, and lies between zero and 19. Telescoping the rank proves that every remaining walk has at most 19 transitions; an explicit walk attains 19. The rank table, universal walk implication and attainment have passed Lean. This establishes a limitation on consecutive residence in that family, with no bound on excursions outside it.

The first two share refinements of longer contexts illustrate the same distinction. A particular ten-transition extension of an earlier cycle has normalized mean $413/100$, whereas the complete ten-transition restricted family has the smaller minimum $2477/600$. An attaining cycle is an upper bound on a minimum, not evidence that all cycles have its mean.

\subsection{Exact history and its limitation}\label{sec:history-recognition}
To use an eleven-transition theorem in the complete nine-transition graph, record the relevant prefix of its three successive nine-direction labels. Each label is normalized by first occurrence of its coordinates. A completed prefix triggers the local count restriction or share inequality. The lifted transition still charges the last five internal centres of its nine-transition suffix, so the boundary parameter remains $n=9$.

The first count restriction adds 15552 states, giving 1041984 states in total. All 11162 canonical induced eleven-direction words were enumerated to check that its three-label signature identifies the required word uniquely. The eight unambiguous count-conditioned share patterns and the two further count restrictions yield a final model with 1166400 states. The share rules strengthen 175293 lifted transitions; the three count restrictions exclude 17161 lifted transitions. The complete transition construction and all numerical potential inequalities were independently reconstructed~\cite{newmodelarchive}.

Canonical labels alone do not always identify the longer word. For example,
\[
\begin{split}
&(0,1,2,3,4,2,1,5,6,3,0),\\
&(0,1,2,3,4,2,1,5,6,3,7)
\end{split}
\]
have identical triples of canonical nine-direction labels. Coordinate 0 has left the retained suffix before the last step, so that suffix does not distinguish its return from a new coordinate. The checked share rule for the first word cannot be applied to the second. That rule is omitted from the complete model; recovering it requires more history or another geometric proof. This explicit ambiguity prevents an unjustified identification of local contexts.

All three final models in the comparison table have exact integer mean $18823/38$. Their potentials have range 23459 at denominator 38, and attaining cycles have 38 transitions. The conditional boundary calculation is
\[
(18823+4200\cdot38)m
\le1099680\cdot38+8\cdot18823+23459,
\]
or
\begin{equation}\label{eq:current-conditional-bound}
178423m\le41961883.
\end{equation}
Its integer consequence remains 235. The first restriction improves the complete mean; the extra shares and two later exclusions leave another attaining cycle. No improvement to the global theorem is asserted.

\subsection{The complete remaining minimum-mean family}
For any edge $u\to v$ with weight $w$, define its nonnegative potential slack by
\[
s(u,v)=d\,w+\pi(u)-\pi(v)-p.
\]
Around a directed cycle, the potential terms cancel. If the cycle has mean $p/d$, its total slack is zero. Since every slack is nonnegative, every edge of that cycle is tight. Conversely, every cycle consisting of tight edges has that mean. Thus the tight edges lying in cyclic strongly connected components identify the entire minimum-mean family.

For the final complete model, this extraction gives one component with 70 states and 99 transitions. The two new count exclusions remove the tested windows of a previous attaining cycle, but alternative cycles in this component preserve the same mean. A stronger empty-square estimate must therefore control the whole remaining family and all possible replacements. The extraction is an exact finite computation under the recorded potential. Its complete relation to arbitrary snakes, and the inherited numerical premises, remain separate proof obligations.

'''
replace(r'\section{Remaining requirements for a stronger bound}',models+r'\section{Remaining requirements for a stronger bound}')
a=s.index('Corollary~\\ref{cor:eighteen-empty} gives the immediate target for 234.',s.index(r'\section{Remaining requirements'))
b=s.index(r'\subsection{Sufficient charge inequalities}',a)
s=s[:a]+r'''Corollary~\ref{cor:eighteen-empty} gives the immediate target for 234. The longer-window calculations strengthen the available local charge, but the complete model still admits the 70-state minimum-mean family described above. The remaining task has two parts: establish sufficient charge for every permitted sequence, including boundary losses, and discharge every local and graph-coverage premise used in that deduction. A finite rank bound on one restricted family does not control the rest of the model. The following targets specify stronger sufficient global inequalities.

'''+s[b:]
replace('The zero-credit cycle identifies a precise failure of the current catalogue\'s coverage, without asserting that this cycle can occur in a snake.','The earlier zero-credit cycle and the current 70-state tight family identify different limitations of their respective catalogues. Neither finite family asserts the existence of a corresponding complete snake.')
replace('The overlap inequalities, reversal transfer, finite rank certificate, and zero-credit limitation have separate Lean checks.','The overlap inequalities, reversal transfer, finite rank certificates, count-saturation deductions and three forced-corner restrictions have separate Lean checks.')
replace('Further work on the selected empty-square route must supply a new valid restriction on the surviving minimum-charge family and account for its frequency and boundary losses.','Further work on the selected empty-square route must strengthen shares over the complete 70-state minimum-charge family, control possible replacement cycles, and account for boundary losses. The most recent contributor proposal toward 234 reduces its certificate set and estimated replay cost, but its remaining certificates and graph checks have not been completed~\\cite{conditional234archive}. It is excluded from the global theorem here.')
replace('Accessed 13 October 2026.\n\\bibitem{ostergard}','Accessed 29 October 2026.\n\\bibitem{ostergard}')
bib=r'''\bibitem{geometricarchive}
I.~Hironaka, T.~Ma, and S.~Zhan. \emph{Forced-absence shares, longer windows and complete critical-family calculations}. Research milestones 57--61, included in pinned revision \texttt{6d7adc03}.
\url{https://github.com/hironaka-iori/Snake-in-the-box-in-9/tree/6d7adc034da38b71fe6210acf5442255a7a52771/milestones}.

\bibitem{choicearchive}
I.~Hironaka, T.~Ma, and S.~Zhan. \emph{Vertex splits, neighbour alternatives and count-saturation share certificates}. Research milestones 62--65, pinned revision \texttt{6d7adc03}.
\url{https://github.com/hironaka-iori/Snake-in-the-box-in-9/tree/6d7adc034da38b71fe6210acf5442255a7a52771/milestones}.

\bibitem{newmodelarchive}
I.~Hironaka, T.~Ma, and S.~Zhan. \emph{Complete-model history, direct count restrictions and manuscript revision}. Research milestone 66, 29 October 2026.
\url{https://github.com/hironaka-iori/Snake-in-the-box-in-9/tree/main/milestones/66-full-model-and-revision}.

\bibitem{conditional234archive}
Snake-in-the-box project contributors. \emph{Conditional seven-centre refinement toward 234 and certificate-cost reduction}. Revision \texttt{852209db}, 29 October 2026. The final proof obligations remain incomplete.
\url{https://github.com/hironaka-iori/Snake-in-the-box-in-9/tree/852209db/milestones/25-k7-234}.

'''
replace(r'\end{thebibliography}',bib+r'\end{thebibliography}')
paper.write_text(s,encoding='utf-8',newline='\n');mirror.write_bytes(paper.read_bytes())
out=dict(before_sha256=before,after_sha256=hashlib.sha256(paper.read_bytes()).hexdigest(),
    prior_statements=len(re.findall(r'\\begin\{(?:theorem|lemma|proposition|corollary|conjecture|definition)\}',old)),
    current_statements=len(re.findall(r'\\begin\{(?:theorem|lemma|proposition|corollary|conjecture|definition)\}',s)),
    scope='Existing paper rewritten and historical model moved to appendix. Source and mathematical checks, built-in compilation and visual inspection remain separate steps.')
(HERE/'data/paper-revision.json').write_text(json.dumps(out,indent=2)+'\n');print(out)
