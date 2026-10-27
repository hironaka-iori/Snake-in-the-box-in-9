from pathlib import Path
import hashlib,json,re,subprocess

HERE=Path(__file__).resolve().parents[1]
ROOT=HERE.parents[1]
paper=ROOT/'paper/snake9_research.tex'
mirror=Path('D:/Codex/2026-10-13/new-chat/outputs/snake9_research.tex')
old=paper.read_text(encoding='utf-8')
assert hashlib.sha256(paper.read_bytes()).hexdigest()=='8473cbc3bacec85ad88e84ef67f43ccf79a1ec37f8b8ae86b288199e028d7ab9'
assert paper.read_bytes()==mirror.read_bytes()
s=old
def replace(a,b):
 global s
 assert s.count(a)==1,(a[:100],s.count(a))
 s=s.replace(a,b)

abstract=r'''Let $a(9)$ denote the largest number of edges in an induced path in the nine-dimensional binary hypercube. The verified construction and the completed contributor proof give $191\le a(9)\le235$. We present the upper-bound argument through its geometric and finite counting steps. Its central identity is $T+2s_0+35(m+1)=9214$, where $T$ counts singleton squares and $s_0$ counts empty squares. A checked local catalogue and state potential give $4m\le T+21$, hence $39m+2s_0\le9200$. Thus eighteen empty squares would suffice to exclude a 235-edge snake. We develop sharp restrictions on singleton counts, five local empty-square share inequalities, and an overlap bound that converts these inequalities into a path charge. The strongest exploratory finite model has exact normalized minimum cycle mean $102/25$, with unreplayed local premises still distinguished from proved rules. A surviving cycle has zero recorded share credit; a telescoping argument shows why reweighting those credits alone cannot improve its mean. Complete witnesses establish the sharpness of selected local inequalities. The value 196 remains an extrapolation without a matching construction or optimality proof. The completed 235 theorem has a successful archived Lean dependency audit; an independent full rebuild of that contributor proof remains pending.'''
a=s.index('\\begin{abstract}')+len('\\begin{abstract}')
b=s.index('\\end{abstract}',a)
s=s[:a]+'\n'+abstract+'\n'+s[b:]
replace(r'\boxed{191\le a(9)\le236.}',r'\boxed{191\le a(9)\le235.}')
replace('gives this argument directly for 236.','gives this argument directly for 235.')
replace(r'$a(9)\le236$ & Geometric window reduction, 732 refutations, a complete potential check, and the endpoint summation.',r'$a(9)\le235$ & Geometric window reduction, 1287 catalogue keys, a complete potential check, and the endpoint summation.')
replace(r'Finite-model mean $42/11$ & A cycle and an integer potential checked on every edge, including after the sharp pair restriction.',r'Finite-model mean $102/25$ & A cycle and an all-edge potential for the current exploratory model; some local premises remain unreplayed.')
replace('Choose two to five consecutive internal centres','Choose two to six consecutive internal centres')

start=s.index(r'\subsection{The radius-four catalogue and state potential}')
end=s.index(r'\section{Sharp restrictions on two singleton counts}',start)
historical=s[start:end]
historical=historical[:historical.index('This completes the dependency chain')]+r'''This earlier proof uses the smaller 732-row catalogue. The six-centre proof in Section~\ref{sec:upper-proof} strengthens its conclusion to 235. The two arguments have separate archived dependency audits. The earlier proof of 238 is retained in Appendix~\ref{app:bound238}.

'''
new=r'''\subsection{The six-centre catalogue and potential}\label{sec:six-centre-235}
Let $\mathcal F_6$ be the completed catalogue of 1287 normalized direction-and-count keys in the contributor archive~\cite{bound235archive}. A key prescribes between two and six consecutive internal counts. As before, a symbol six denotes the interval $[6,21]$. A state consists of a normalized induced seven-direction word and the last five internal count symbols. There are $34\cdot6^5=264384$ states. A transition appends one direction and one count, discards the oldest entries, and renormalizes the directions. It is permitted if the resulting eight-direction word is induced and the new windows avoid the catalogue in both orientations.

\begin{lemma}[Six-centre exclusions and potential]\label{lem:six-centre-235}
Every snake avoids $\mathcal F_6$. There is an integer potential $\Psi$ on the stated finite state set, with $0\le\Psi\le7$, such that every permitted transition $u\to w$ with appended count $b$ satisfies
\begin{equation}\label{eq:six-centre-step}
4+\Psi(w)\le b+\Psi(u).
\end{equation}
\end{lemma}
\begin{proof}[Computer-assisted proof]
Normalize a hypothetical occurrence by translation and coordinate permutation. Its selected vertices satisfy the degree conditions, the two-endpoint restriction, and the exact missing-corner counts. Lemma~\ref{lem:subset-low-degree} justifies the cycle exclusions. The counter identities in Appendix~\ref{app:counters} interpret the auxiliary threshold variables. Each catalogue key is discharged by a checked refutation or an implication from a previously refuted key. A refutation derives the empty clause from input clauses already proved necessary for the hypothetical snake. The archive assembles the reused refutations and 635 new certificates into the complete catalogue assertion.

There are 132 normalized induced eight-direction words. Each is checked against all $6^6$ count choices, covering $132\cdot6^6=6158592$ candidate transitions. The finite potential assertion is verified on every permitted transition. The geometric interpretation, catalogue coverage, potential check, and universal path summation are included in the completed contributor theorem and its saved dependency audit~\cite{bound235archive}. The independent numerical reconstruction retains 3546419 permitted transitions and verifies a potential of range five; the weaker bound seven above is the bound used in the checked universal argument. An independent rebuild of the entire contributor dependency closure remains pending.
\end{proof}

\begin{proposition}[Singleton estimate with boundary terms]\label{prop:count-235}
Every nontrivial $m$-edge snake in $\Q_9$ satisfies
\begin{equation}\label{eq:count-235}
4m\le T+21.
\end{equation}
\end{proposition}
\begin{proof}
Suppose $m\ge7$. Write $d_i$ for the direction joining $x_i$ to $x_{i+1}$. At index $i$, the state records $d_i,\ldots,d_{i+6}$ and $b_{i+2},\ldots,b_{i+6}$. Its next transition appends $b_{i+7}$. Summing~\eqref{eq:six-centre-step} over the $m-7$ transitions gives
\[
4(m-7)+\Psi_{m-7}\le\sum_{j=7}^{m-1}b_j+\Psi_0.
\]
The first six internal singleton counts contribute at least six and the two endpoints contribute at least eight. Hence $\sum_{j=7}^{m-1}b_j\le T-14$. Using $0\le\Psi\le7$ gives
\[
4m-28\le T-14+7=T-7,
\]
which proves the assertion. For $1\le m<7$, positivity and the endpoint bounds give $T\ge m+7$, and $4m\le m+28\le T+21$.
\end{proof}

\begin{theorem}[Retained empty-square bound]\label{thm:upper235}
Every nontrivial $m$-edge snake in $\Q_9$ satisfies
\begin{equation}\label{eq:retained-empty-235}
\boxed{39m+2s_0\le9200.}
\end{equation}
In particular, $m\le235$.
\end{theorem}
\begin{proof}
Substitute $T\ge4m-21$ into $T+2s_0+35(m+1)=9214$. This gives $39m+2s_0+14\le9214$. Since $s_0\ge0$ and $39\cdot236=9204>9200$, integrality gives $m\le235$. The zero-edge path satisfies the upper bound directly. Together with Theorem~\ref{thm:lower}, this proves Theorem~\ref{thm:main}.
\end{proof}

\begin{corollary}[Eighteen-empty-square target]\label{cor:eighteen-empty}
A snake with at least eighteen empty squares has at most 234 edges. It therefore suffices to prove $s_0\ge18$ for every hypothetical 235-edge snake in order to improve the universal upper bound to 234.
\end{corollary}
\begin{proof}
Equation~\eqref{eq:retained-empty-235} gives $39m\le9164<39\cdot235=9165$. The threshold cannot be reduced using this inequality alone: the numerical pair $(m,s_0)=(235,17)$ satisfies it. This numerical consistency asserts no realizing snake. The retained-identity arithmetic and the threshold implications have been checked in Lean under their stated count and incidence premises.
\end{proof}
The following sections retain the empty-square term through local share inequalities. They also describe restrictions on singleton counts needed to interpret those inequalities. The earlier 236 proof is preserved in Appendix~\ref{app:bound236}.

'''
s=s[:start]+new+s[end:]
replace('\\appendix\n','\\appendix\n\\section{The preceding radius-four bound of 236}\\label{app:bound236}\n'+historical)

small=r'''\subsection{Short return and low-count restrictions}\label{sec:short-returns}
In the following statements a direction word starts at $x_r$, and distinct letters denote distinct coordinates. The singleton counts refer to the full snake.

\begin{proposition}[Three exclusions of a singleton count]\label{prop:three-singleton-exclusions}
The following implications hold without restrictions on other counts:
\[
\begin{array}{c|c}
\text{directions}&\text{conclusion}\\\hline
(a,b,c,d,a,e)&\alpha_{r+4}\ge2\\
(a,b,c,d,a,e,b)&\alpha_{r+1}\ge2\\
(a,b,c,d,a,c,e,d)&\alpha_{r+7}\ge2
\end{array}
\]
\end{proposition}
\begin{proof}[Computer-assisted proof]
Impose the indicated count at most one in the necessary radius-four model. The three refutations have respectively 282, 456, and 829 input clauses. The missing-corner interpretation, all retained path clauses, refutations, and transport to arbitrary labels pass the recorded Lean checks~\cite{recentarchive}. Positivity then gives each asserted bound. For the first row there is also a geometric explanation: at $x=x_{r+4}$ the opposite corner $x+e_b+e_c=x_{r+1}+e_d$ is unselected. If this were the unique missing pair, the singleton continuation restriction would force the second step along the arm through $x_{r+5}$ to use $b$ or $c$. Its prescribed coordinate is $e$, a contradiction. The finite proof independently checks the needed exclusion. Sharpness of two for complete snakes is unresolved.
\end{proof}

\begin{proposition}[Compatibility of small counts]\label{prop:small-count-compatibility}
The following implications hold:
\[
\begin{array}{c|l}
(a,b,c,d,a,b)&\alpha_{r+1}+\alpha_{r+5}\ge5\\
(a,b,c,d,a,e,b,a)&\alpha_{r+4}+\alpha_{r+7}\ge6\\
(a,b,c,d,e,c)&\alpha_{r+1}\le3\ \Longrightarrow\ \alpha_{r+5}\ge3.
\end{array}
\]
\end{proposition}
\begin{proof}[Computer-assisted proof]
For the first two rows, a joint threshold counter represents the indicated sum, with multiplicity preserved if a Boolean variable contributes at both centres. Adding the contrary bounds four and five gives refuted cores of 2228 and 1467 clauses. The third row excludes the simultaneous caps three and two with a 1094-clause core. The additional cycle exclusions in the first two cases follow from Lemma~\ref{lem:subset-low-degree}. All clause interpretations, replays, and arbitrary-coordinate implications have passed Lean~\cite{recentarchive}. Local forests attain the first two lower bounds; complete-snake sharpness is unproved. The third assertion is directional: reversing it requires reversing the full direction word as well as the counts.
\end{proof}

\begin{theorem}[Sharp return inequalities]\label{thm:sharp-returns}
For consecutive directions $(a,b,c,a)$,
\[
\alpha_{r+1}+\alpha_{r+3}\ge5.
\]
For consecutive directions $(a,b,c,d,e,a)$,
\[
\alpha_{r+1}+\alpha_{r+4}+\alpha_{r+5}\ge13.
\]
Both constants are attained by complete snakes in $\Q_9$.
\end{theorem}
\begin{proof}[Computer-assisted proof]
The contrary sum caps four and twelve are excluded in the necessary geometric models by replayed refutations and checked counter interpretations. The second refutation has 3593 core clauses and 10807572 antecedent references. The arbitrary-coordinate deductions and complete witnesses are checked in Lean~\cite{recentarchive}. The 146-edge witness in Appendix~\ref{app:return-witnesses} attains counts $(2,3)$ at offsets one and three of a segment starting at index 95. The 143-edge witness attains $(3,5,5)$ at offsets one, four, and five of a segment starting at index 64. Thus neither constant admits a universal increase under its stated direction hypothesis.
\end{proof}

A complete six-direction survey considers the nine normalized induced words, ten pairs of internal positions, and four caps $(2,2),(2,3),(3,2),(3,3)$. Of the 360 tests, 50 have checked exclusions and 310 have verified acyclic local assignments. The exclusions follow from 33 replayed shorter premises. Appendix~\ref{app:pair-caps} records the maximal forbidden caps. A positive local assignment proves feasibility of the local conditions only. It need not extend to a complete snake. Neither this catalogue nor the sharp triple inequality removes the earlier model's mean-$42/11$ obstruction by itself.

'''
replace(r'\section{Compatibility between overlapping windows}',small+r'\section{Compatibility between overlapping windows}')

shares=r'''\subsection{Five-centre share inequalities}\label{sec:five-shares}
Write $\Sigma=\sum_{x\in S}\sigma_{12}(x)$. Proposition~\ref{prop:share-loss} gives $\Sigma\le48s_0$ and
\begin{equation}\label{eq:share-budget-12}
G_{12}=24T+\Sigma,\qquad G_{12}+840(m+1)\le221136.
\end{equation}

\begin{theorem}[Five-centre share bounds]\label{thm:five-shares}
Suppose six consecutive directions beginning at $x_r$ and the five internal singleton counts satisfy a row of the following table. Distinct letters denote distinct coordinates; each of $A,B,C$ that occurs lies in $[6,21]$. Then $\sum_{j=1}^{5}\sigma_{12}(x_{r+j})\ge L$, with $L$ as displayed.
\[
\begin{array}{c|c|r}
\text{directions}&(\alpha_{r+1},\ldots,\alpha_{r+5})&L\\\hline
(a,b,c,d,b,e)&(3,3,3,A,5)&48\\
(a,b,c,d,e,f)&(3,A,2,3,B)&96\\
(a,b,c,a,d,e)&(A,3,B,3,3)&96\\
(a,b,c,d,e,f)&(4,A,2,3,B)&96\\
(a,b,c,d,a,e)&(A,B,2,2,C)&96
\end{array}
\]
Every row also holds with the direction word and count tuple both reversed.
\end{theorem}
\begin{proof}[Computer-assisted proof]
Use the union of radius-four neighborhoods around the five centres. All neighbors of each centre, all squares incident to those neighbors, and all vertices needed for their selected-neighbor counts are represented. A hypothetical snake therefore determines the exact integer shares as well as the singleton counts in this model. Since each centre is selected, every denominator in its share is positive. Threshold counters encode the empty-square and selected-neighbor counts; their interpretation gives exactly $\lfloor12e(q)/d(q)\rfloor$ for each summand.

Assume the sum is at most $L-1$. The path, count, share, and cap clauses then have a refutation. In table order, the trimmed cores contain 6681, 7208, 14471, 11582, and 11751 clauses. Each retained clause is proved necessary for the hypothetical snake, and each refutation is replayed by the sound checker. The geometric interpretations and arbitrary-coordinate applications have completed Lean checks~\cite{recentarchive}. This proves the five bounds. Reversal preserves the selected set and hence $e(q)$, $d(q)$, and every vertex share; it reverses precisely the five counted centres. The sum is unchanged. The reversal implication is checked separately.
\end{proof}
Ordinary local forests matching these five rows have share sums 263, 307, 378, 855, and 450, respectively. They show that the corresponding ordinary local conditions are consistent. They establish neither full-snake realizability nor sharpness of the stated share bounds.

\begin{corollary}[Sufficient occurrence counts]\label{cor:share-occurrences-234}
Nine pairwise disjoint five-centre occurrences with $L=96$ imply $m\le234$. Alternatively, 43 such occurrences with distinct starting positions suffice, allowing overlap.
\end{corollary}
\begin{proof}
Disjoint occurrences give $\Sigma\ge9\cdot96=864$, hence $s_0\ge18$. For arbitrary distinct starts, any position lies in at most five windows, so $5\Sigma\ge43\cdot96=4128$. Combining with $\Sigma\le48s_0$ gives $240s_0\ge4128>240\cdot17$, again $s_0\ge18$. Apply Corollary~\ref{cor:eighteen-empty}. The numerical implications and overlap accounting have passed Lean. Neither required occurrence frequency is established for arbitrary snakes.
\end{proof}

'''
replace(r'\subsection{Short return and low-count restrictions}',shares+r'\subsection{Short return and low-count restrictions}')

aggregate=r'''\subsection{Five-window accounting and the current obstruction}\label{sec:current-charge}
For each represented state transition indexed by $i$, take the largest applicable lower bound $L_i$ on the five centres $i+3,\ldots,i+7$, using zero if no recorded rule applies. Bounds on the same window are combined by their maximum. Put
\[
B=\sum_{j=7}^{m-1}b_j,\qquad W=\sum_{i=0}^{m-8}(120b_{i+7}+L_i).
\]
Assume $m\ge7$, with empty sums when $m=7$.

\begin{proposition}[Five-window charge budget]\label{prop:five-budget}
For any valid choice of these share bounds,
\[
W+1680\le5G_{12}.
\]
If a state potential of range at most $R$ satisfies $p+\pi(w)\le d(120b+L)+\pi(u)$ on every transition traced by the snake, where $p,d$ are positive integers, then
\begin{equation}\label{eq:five-potential-bound}
(p+4200d)m\le1099800d+7p+R.
\end{equation}
\end{proposition}
\begin{proof}
Each position lies in at most five of the windows, so $\sum_i L_i\le5\Sigma$. The six omitted internal counts and two endpoints give $B+14\le T$. Thus
\[
W+1680=120B+\sum_iL_i+120\cdot14\le120T+5\Sigma=5G_{12}.
\]
Telescoping the potential inequalities gives $p(m-7)\le dW+R$. Equation~\eqref{eq:share-budget-12} and the preceding bound give $W+4200m\le1099800$. Combining yields~\eqref{eq:five-potential-bound}. The overlap, algebraic, and conditional path implications have been checked in Lean; the hypotheses still require a complete graph-to-snake assembly for each generated model.
\end{proof}

The current product graph uses 264384 states, as in the six-centre proof. The following exact finite-model means are established by an attaining cycle and an integer potential checked on every retained transition. The normalized charge is $(120b+L)/120$.
\begin{center}
\begin{tabular}{p{0.60\textwidth}rr}
\toprule
Restrictions and share rules & Mean & Edges\\\midrule
Completed 235 catalogue; counts only & $4$ & 3546419\\
All recorded numerical count exclusions; counts only & $65/16$ & 3042898\\
Same exclusions; first four proved share rows & $57/14$ & 3042898\\
Five further count exclusions and eight numerical share rules, in both orientations & $53/13$ & 3042328\\
Same model; fifth proved share row in both orientations & $102/25$ & 3042328\\
\bottomrule
\end{tabular}
\end{center}
The last four rows use ordinary exclusions that have not all been replayed. The last two also retain eight numerical share premises. These are finite-model comparisons under explicit rule catalogues; they do not supply a stronger universal theorem. Even with all their premises accepted, the displayed means and boundary losses give an integer edge estimate of 235. For the last row, the potential has $p=2448$, $d=5$, and range $R=3216$, giving $977m\le229973$.

The fifth share row was selected using the entire preceding minimum-mean component: 57 states and 83 edges. Its pattern labels four edges, and deleting those edges leaves an acyclic graph. An integer rank strictly increases along every remaining edge. Therefore every nonempty closed walk in that component uses the selected pattern. This finite rank argument has been checked in Lean. It explains why one inequality increases the mean from $53/13$ to $102/25$, while leaving open the behavior of replacement cycles.

\begin{proposition}[Zero-credit cycle limitation]\label{prop:zero-credit}
The current exploratory graph contains a 25-step cycle whose appended counts sum to 102 and whose recorded share lower bounds all vanish. Any potential inequality using only these recorded share credits has normalized cycle mean at most $102/25$. Selecting or reweighting these zero credits cannot increase the charge on this cycle.
\end{proposition}
\begin{proof}
The cycle's appended count sequence is
\[
\begin{gathered}
(6,6,2,5,2,6,3,6,3,2,6,4,3,\\
6,3,4,6,2,3,6,3,6,2,5,2).
\end{gathered}
\]
The saved state transitions close cyclically, each recorded share lower bound is zero, and the counts sum to 102. These finite data are independently checked against the preceding graph archive. Summing $A+\pi_{i+1}\le B b_i+\pi_i$ around the cycle cancels the potentials and gives $25A\le102B$. Every nonnegative weighted sum of the zero credits is zero, including every disjoint packing. Lean checks the displayed sum, general telescoping implication, and zero-credit packing identity.

Even with no potential loss, this ceiling cannot exclude 235 through the corresponding single-copy charge accounting. Indeed $25p\le2448d$ implies
\[
(p+840d)235\le219960d+7p+R\qquad(R\ge0).
\]
This arithmetic implication is also checked in Lean. The limitation concerns the present recorded lower bounds and finite relaxation. It asserts neither zero actual shares nor realization of the cycle in a complete snake.
\end{proof}

A new local inequality must assign positive credit to this surviving family, or a valid additional restriction must exclude its relevant transitions. Increasing constants of rules absent from the cycle, or optimizing their packing, leaves this obstruction unchanged. One sufficient future path target is normalized mean $21/5$ with potential range at most 2111 in the weights $120b+L$. Substituting $p=504$ and $d=1$ into~\eqref{eq:five-potential-bound} gives $4704m\le1105439<4704\cdot235$, hence 234. This is a checked conditional target, without an established universal potential of that strength.

'''
replace(r'\section{Remaining requirements for a stronger bound}',aggregate+r'\section{Remaining requirements for a stronger bound}')
replace(r'\subsection{What the enlarged finite model establishes}',r'\subsection{The earlier seven-centre model}')
replace('The resulting computational model retains seven normalized directions','The earlier computational model retains seven normalized directions')
replace('The local theorems and common budget reduce the remaining upper-bound task to coverage:', 'Corollary~\\ref{cor:eighteen-empty} gives the immediate target for 234. Proposition~\\ref{prop:zero-credit} rules out improving the current model solely by repacking its recorded credits. The local theorems and common budget reduce the remaining upper-bound task to coverage:')
replace('Weighted packing preserves more of the available local information while leaving those proof obligations explicit.', 'Weighted packing is valid under the stated capacities; it supplies no additional credit on the zero-credit cycle of Proposition~\\ref{prop:zero-credit}. The targets 230 and 231 remain longer-term conditional estimates.')

a=s.index(r'\section{Verification scope and remaining problem}')
b=s.index('\\appendix',a)
s=s[:a]+r'''\section{Verification scope and remaining problem}\label{sec:verification}
The global conclusion assembled here is $191\le a(9)\le235$. The lower bound follows from the explicit witness. The upper bound uses the square identity, endpoint estimates, all 1287 catalogue keys, a potential verified on every permitted transition, and the path summation. The main argument includes all initial-count and potential losses. No conjecture or restricted construction search enters it.

The completed contributor theorem has a successful archived dependency audit~\cite{bound235archive}. Its assumptions have been discharged in that development; the audit lists propositional extensionality, classical choice, and quotient soundness. The final theorem source and saved audit were reviewed, and the potential was independently reconstructed. A fresh independent rebuild of the entire 235 dependency closure remains pending. The preceding 236 and 238 proof archives are retained separately with their own recorded audits. Appendix~\ref{app:bound236} presents the 236 summation in full; Appendix~\ref{app:bound238} preserves the 238 argument.

The local restrictions and share bounds have the scopes stated in their proofs. Their checked deductions include normalization to arbitrary coordinate labels, semantic interpretation of the finite clauses, and replay of the contradictions. The sharp return witnesses are complete paths. The overlap inequalities, reversal transfer, finite rank certificate, and zero-credit limitation have separate Lean checks. All cited local dependency audits use only the standard axioms listed above. A local forest supplies only a feasible local assignment; it is not a complete-snake witness.

The successive exploratory graph means are proved as finite statements by an attaining cycle and an all-edge integer-potential check. Some of their count and share rules are still unreplayed solver exclusions, and the complete Lean assembly from arbitrary snakes into these generated graphs remains pending. Their numerical means do not improve the global theorem. Timeouts establish neither existence nor impossibility. The zero-credit cycle identifies a precise failure of the current catalogue's coverage, without asserting that this cycle can occur in a snake.

The optimum remains unresolved. No construction above 191 edges has been obtained here. The immediate upper-bound question is whether every hypothetical 235-edge snake has at least eighteen empty squares, or an equivalent sufficiently strong charge. Further work on the selected empty-square route must supply a new valid restriction on the surviving minimum-charge family and account for its frequency and boundary losses. The conjecture $a(9)=196$ requires both a 196-edge construction and a universal exclusion of 197 edges.

'''+s[b:]

caps=r'''\section{Complete six-direction pair-cap catalogue}\label{app:pair-caps}
A word begins at index $r$; the pair $(i,j)$ refers to $\alpha_{r+i},\alpha_{r+j}$. An entry $(u,v)$ forbids the simultaneous upper caps $\alpha_{r+i}\le u$, $\alpha_{r+j}\le v$. The table lists all componentwise maximal forbidden caps within $\{2,3\}^2$ from the complete 360-test survey. Smaller caps follow by implication. Every listed exclusion is Lean checked; all other tested cases have independently verified local forests~\cite{recentarchive}.
\begin{longtable}{lll}
\toprule Word & Position pair & Maximal forbidden caps\\\midrule\endhead
012031&(1,3), (1,4)&(2,2)\\
012031&(1,5)&(2,3), (3,2)\\
012032&(1,3), (2,5)&(3,2)\\
012032&(1,4), (3,5)&(2,3)\\
012032&(2,4)&(3,3)\\
012034&(1,3)&(3,2)\\
012034&(1,4), (2,4)&(2,2)\\
012034&(1,5)&(2,3)\\
012301&(1,5)&(2,2)\\
012304&(1,5)&(2,3), (3,2)\\
012304&(4,5)&(2,2)\\
012310&(1,2), (1,4), (2,5), (4,5)&(2,2)\\
012310&(1,3)&(3,2)\\
012310&(2,4)&(2,3), (3,2)\\
012310&(3,5)&(2,3)\\
012314&(2,4)&(2,2)\\
012340&(1,2), (4,5)&(2,2)\\
012340&(1,5)&(2,3), (3,2)\\
012345&(1,2), (4,5)&(2,2)\\
012345&(1,5)&(2,3), (3,2)\\\bottomrule
\end{longtable}

'''
replace(r'\section{Geometric restrictions and intermediate bounds}',caps+r'\section{Geometric restrictions and intermediate bounds}')

# Append the two complete sharpness witnesses in vertex form, with a direct audit.
spec=[('49-six-direction-pair-catalogue','witness-return.json',146,95,[1,3],[2,3]),('50-three-count-return','witness.json',143,64,[1,4,5],[3,5,5])]
witness_text='\\section{Complete witnesses for the return inequalities}\\label{app:return-witnesses}\nThe following vertex lists use binary integer encoding. Each consecutive pair differs in one coordinate, and all other pairs differ in at least two coordinates. Singleton counts are recomputed against the entire selected set.\n'
witness_receipts=[]
for folder,name,length,r,offsets,expected in spec:
 data=json.loads((ROOT/'milestones'/folder/'data'/name).read_text())
 vertices=data.get('vertex_sequence',data.get('vertices'))
 assert vertices is not None,data.keys()
 assert len(vertices)==length+1 and len(set(vertices))==len(vertices)
 pairs=0
 for i,x in enumerate(vertices):
  assert 0<=x<512
  for j in range(i+1,len(vertices)):
   assert ((x^vertices[j]).bit_count()==1)==(j==i+1)
   pairs+=1
 selected=set(vertices)
 actual=[sum(all(y not in selected for y in [vertices[r+k]^(1<<a),vertices[r+k]^(1<<b),vertices[r+k]^(1<<a)^(1<<b)]) for a in range(9) for b in range(a+1,9)) for k in offsets]
 assert actual==expected,(actual,expected)
 witness_receipts.append(dict(edges=length,start=r,pair_checks=pairs,offsets=offsets,counts=actual))
 witness_text+=f'\\subsection{{A {length}-edge witness}}\nThe selected return starts at index ${r}$; its counted offsets are $('+','.join(map(str,offsets))+')$ and its counts are $('+','.join(map(str,actual))+')$.\n\\[\n\\begin{gathered}\n'
 rows=[','.join(map(str,vertices[i:i+15])) for i in range(0,len(vertices),15)]
 witness_text+='\\\\\n'.join(rows)+'\n\\end{gathered}\n\\]\n'
replace(r'\section{Finite verification of the printed witnesses}',witness_text+r'\section{Finite verification of the printed witnesses}')

bib=r'''\bibitem{bound235archive}
Snake-in-the-box project contributors. \emph{Completed six-centre bound of 235: proof assembly and dependency audit}. Pinned audit revision \texttt{b20346ee}; later source state \texttt{74ca83db}.
\url{https://github.com/hironaka-iori/Snake-in-the-box-in-9/tree/b20346ee15a43b96de34128bc66b05551244cf31}.

\bibitem{recentarchive}
I.~Hironaka, T.~Ma, and S.~Zhan. \emph{Short-return inequalities, empty-square share certificates, and finite-model coverage}. Research milestones 47--55, pinned revision \texttt{c6246609}.
\url{https://github.com/hironaka-iori/Snake-in-the-box-in-9/tree/c62466095bbbda5c79163364eadffc6e98d91a7c/milestones}.

'''
replace(r'\end{thebibliography}',bib+r'\end{thebibliography}')
assert re.search(r'\\hypersetup\{[\s\S]*?\n\}',s).group()==re.search(r'\\hypersetup\{[\s\S]*?\n\}',old).group()
assert re.search(r'\\author\{.*\}',s).group()==re.search(r'\\author\{.*\}',old).group()
oldlabels=set(re.findall(r'\\label\{([^}]+)\}',old))
labels=re.findall(r'\\label\{([^}]+)\}',s)
assert oldlabels<=set(labels) and len(labels)==len(set(labels))
refs=set(re.findall(r'\\(?:eqref|ref)\{([^}]+)\}',s))
assert refs<=set(labels),refs-set(labels)
assert '.lean' not in s
paper.write_text(s,encoding='utf-8',newline='\n');mirror.write_bytes(paper.read_bytes())
(HERE/'data/paper-revision.json').write_text(json.dumps(dict(before_sha256=hashlib.sha256(old.encode()).hexdigest(),after_sha256=hashlib.sha256(paper.read_bytes()).hexdigest(),old_label_count=len(oldlabels),new_label_count=len(labels),all_old_labels_preserved=True,authors_preserved=True,hypersetup_preserved=True,mirror_equal=True,new_witnesses=witness_receipts),indent=2)+'\n')
print(json.dumps(dict(lines=len(s.splitlines()),labels=len(labels),witnesses=witness_receipts)))
