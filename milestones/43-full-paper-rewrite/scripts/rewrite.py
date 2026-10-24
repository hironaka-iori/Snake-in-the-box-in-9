"""Reorganize the existing paper; preserve every prior mathematical statement."""
from pathlib import Path
import hashlib, json, re
ROOT = Path(__file__).resolve().parents[3]
HERE = Path(__file__).resolve().parents[1]
EDITOR = Path('D:/Codex/2026-10-13/new-chat/outputs/snake9_research.tex')
PAPER = ROOT/'paper/snake9_research.tex'
original = EDITOR.read_text(encoding='utf-8')
assert original == PAPER.read_text(encoding='utf-8')
assert r'\label{sec:common-budget}' not in original
s = original

def replace(old, new):
    global s
    assert s.count(old) == 1, (s.count(old), old[:100])
    s = s.replace(old, new)

abstract = r'''Let $a(9)$ denote the maximum edge length of an induced path in the nine-dimensional binary hypercube. We assemble the bound $191\le a(9)\le236$ and develop local restrictions for improving it. The upper bound follows from the exact square identity $T+2s_0+35v=9214$, where $v$ is the number of path vertices, $T$ counts singleton squares, and $s_0$ counts empty squares. A family of 732 excluded local windows yields an integer potential inequality; summation, including all boundary and endpoint contributions, gives $42(v-1)\le11T+203$ and hence $a(9)\le236$. We then retain part of the empty-square contribution through integer shares, prove sharp distance-three count inequalities and conditional distance-four restrictions, and derive a common budget for overlapping count excesses. A larger finite-state model incorporating the identified restrictions still has normalized minimum cycle mean $42/11$. This exact computation concerns the finite model; its eleven critical windows have only numerical exclusions in a stronger local model. Explicit constructions establish the lower bound and distinguish endpoint maximality, local feasibility, and global optimality. The extrapolated value 196 remains a conjecture. The archived complete 236 theorem has a successful Lean dependency audit; a clean independent rebuild remains pending.'''
start = s.index(r'\begin{abstract}')+len(r'\begin{abstract}')
end = s.index(r'\end{abstract}')
s = s[:start]+'\n'+abstract+'\n'+s[end:]

oldroad = r'''Theorem~\ref{thm:lower} proves the lower bound from a displayed sequence. The upper bound is deduced in Theorem~\ref{thm:upper236}. Section~\ref{sec:upper-proof} first develops the argument for 238 and then proves its radius-four strengthening to 236. Its logical dependencies are as follows. Every selected vertex has at least one singleton square, and every endpoint has at least four. The exact square census converts a lower bound on the sum of these counts into an upper bound on length. A finite family of local exclusions supplies a potential inequality, whose sum gives the required lower bound. The computer-assisted steps are identified explicitly; the numerical search outcomes in the appendices are separate from these proof premises.'''
newroad = r'''The lower bound is verified from the explicit transition sequence in Theorem~\ref{thm:lower}. The proof of the upper bound has three steps. First, count coordinate squares exactly and establish positive singleton counts, with a stronger contribution at each endpoint. Second, exclude a finite family of local configurations and verify an integer potential on every remaining transition. Third, sum the potential inequalities and substitute the resulting count estimate into the square identity. Section~\ref{sec:upper-proof} gives this argument directly for 236.

The subsequent sections investigate the information omitted by that bound. Pair inequalities restrict which singleton counts can coexist; integer shares retain some empty-square contributions; and joint-window restrictions recover count excess lost by truncation. Section~\ref{sec:common-budget} combines these contributions under one overlap rule and identifies the obstruction that survives in the resulting finite model. Construction criteria and the numerical conjecture are treated separately, since neither supplies a premise for the upper-bound proof. Detailed earlier bounds, finite catalogues, and restricted search records are retained in the appendices.

\begin{center}
\begin{tabular}{p{0.27\textwidth}p{0.62\textwidth}}
\toprule
Claim & Evidence and scope\\\midrule
$a(9)\ge191$ & An explicit snake with every vertex pair checked.\\
$a(9)\le236$ & Geometric window reduction, 732 refutations, a complete potential check, and the endpoint summation.\\
Further local inequalities & The stated geometric hypotheses and checked local proofs; they do not yet lower 236.\\
Finite-model mean $42/11$ & An attaining cycle and an integer potential checked on every retained edge of the saved graph.\\
$a(9)=196$ & A numerical extrapolation requiring both a construction and a next-length exclusion.\\
\bottomrule
\end{tabular}
\end{center}'''
replace(oldroad, newroad)

# Give count truncation a single early definition used by every later section.
notation = r'''Whenever a statement uses both endpoints, assume $m\ge1$. The single-vertex path is handled separately in each global bound.'''
replace(notation, notation+r'''
For an internal vertex define
\[
b_i=\min\{6,\alpha_i\},\qquad \delta_i=\alpha_i-b_i.
\]
Thus $\alpha_i=b_i+\delta_i$ with $\delta_i\ge0$. A count symbol $b_i<6$ specifies the exact count; $b_i=6$ represents every count from six through twenty-one. Lemma~\ref{lem:window-missing-corners} explains the upper value twenty-one. When these quantities are summed over the whole path, the same definitions are used at the endpoints, without asserting the internal upper bound there.''')

# Extract the earlier 238 development intact and relocate it beside its catalogue.
a = s.index(r'\subsection{The finite exclusion family}')
b = s.index(r'\subsection{The radius-four refinement to 236}')
historical = s[a:b]
s = s[:a]+s[b:]
historical = historical[:historical.index('This first bound uses neither')]
historical = historical.replace(r'\subsection{The finite exclusion family}', r'\subsection{The radius-three exclusion family}')
historical = historical.replace('states. A permitted transition', 'states. A permitted transition')
replace(r'\section{From local exclusions to the bounds 238 and 236}\label{sec:upper-proof}',r'''\section{The upper bound 236}\label{sec:upper-proof}
The square identity reduces the upper-bound problem to a lower estimate for $T$. We obtain that estimate from necessary conditions on short path segments. The local conditions exclude configurations, the finite potential combines the exclusions, and the final summation accounts for the ends of the path.''')
replace(r'''\subsection{The radius-four refinement to 236}\label{sec:radius-four-236}
Replace the radius-three neighborhood by the union of the Hamming balls of radius four around the prescribed centres. Retain the same count symbols, state representation, normalization, and necessary degree, endpoint, and acyclicity conditions. Let $\mathcal F_4$ be the family of 732 normalized direction-and-count pairs in the supplementary catalogue~\cite{radiusfourarchive}. Each pair specifies two to five consecutive internal centres, with the symbol six still representing the interval $[6,21]$. The catalogue, its geometric interpretation, and the potential table are fixed proof data.''',r'''\subsection{The radius-four catalogue and state potential}\label{sec:radius-four-236}
For each prescribed window, use the union of the Hamming balls of radius four around its internal centres. Let $\mathcal F_4$ be the family of 732 normalized direction-and-count pairs in the supplementary catalogue~\cite{radiusfourarchive}. Each pair specifies two to five consecutive internal centres. Count symbols are the truncated values $b_i$, so six represents the interval $[6,21]$.

There are 34 normalized induced direction words of length seven. A state records one such word and the last four internal count symbols. Hence the state set has $34\cdot6^4=44064$ elements. A transition appends one direction and one count, deletes the oldest entries, and renormalizes the directions. It is permitted when the resulting eight-direction word is induced and every new two- through five-centre window avoids $\mathcal F_4$ in both orientations. Every snake determines a sequence of permitted transitions once the catalogue exclusions are proved.

The catalogue and potential table are fixed finite proof data. Their verification has two distinct parts. A hypothetical snake must first satisfy every retained input clause of its local model. A sound contradiction checker then shows that those clauses cannot all hold. The threshold-counter equivalence in Appendix~\ref{app:counters} interprets the auxiliary count variables. For each derived clause, the checker proves that satisfaction of its cited premises implies satisfaction of that clause; reaching the empty clause contradicts satisfaction of the input. A solver's infeasibility report alone is insufficient for this argument.''')
replace(r'There is a nonnegative integer potential $\Psi$ on the same 44064 states', r'There is a nonnegative integer potential $\Psi$ on the 44064 states just defined')
replace('replayed through the sound proof checker described above', 'replayed through the sound contradiction checker')
replace(r'''Use the states indexed by $i$ in the proof of Lemma~\ref{lem:internal-total}, and let $\Psi_i$ be their new potentials.''',r'''Index the transitions by $d_0,\ldots,d_{m-1}$, where $d_i$ joins $x_i$ to $x_{i+1}$. For $0\le i\le m-7$, let the state at $i$ record $d_i,\ldots,d_{i+6}$ and $b_{i+3},\ldots,b_{i+6}$, and denote its potential by $\Psi_i$. Its next transition appends $b_{i+7}$.''')
replace(r'''All 732 local premises of this theorem have been discharged in the archived development. The recorded build and the independent checks made for this revision have different scopes, detailed in Section~\ref{sec:verification}. The theorem still discards $s_0$; the subsequent share estimates retain information omitted from this bound.''',r'''This completes the dependency chain for Theorem~\ref{thm:main}: the explicit sequence gives 191, and the catalogue, potential, and square identity give 236. All 732 local premises have been discharged in the archived development. Section~\ref{sec:verification} records the build evidence and the remaining independent-rebuild limitation. Appendix~\ref{app:bound238} retains the preceding 175-window proof of 238. The present bound uses only $s_0\ge0$; the empty-square shares below retain more of this nonnegative term.''')
marker = r'\section{The complete exclusion catalogue for 238}\label{app:exclusion-catalogue}'
replace(marker, r'''\section{The 175-window proof of the earlier bound 238}\label{app:bound238}
This appendix records the smaller radius-three proof independently of the stronger radius-four bound in the main text. It uses the same square identity, normalization, missing-corner interpretation, and endpoint contributions. Its 175 excluded windows are printed in the following appendix.

'''+historical+'\n'+marker)

# Integrate the completed accounting part of the latest round, with its exact scope.
common = r'''\section{Combining local contributions without repeated counting}\label{sec:common-budget}
Several local theorems may demand excess from the same path position. Their separate charge bonuses cannot be added without checking this overlap. The following result gives one common accounting rule for all seven-centre windows.

\begin{proposition}[Common seven-centre excess budget]\label{prop:common-budget}
Let $J$ be a set of starting indices with $r+8\le m$. For each $r\in J$, let $D_r$ be a nonnegative integer satisfying
\[
D_r\le\sum_{k=1}^{7}\delta_{r+k}.
\]
Then
\[
\sum_{r\in J}D_r\le7\sum_{j=0}^{m}\delta_j.
\]
If several valid lower demands are available for the same window, their maximum may be used as $D_r$.
\end{proposition}
\begin{proof}
Sum the local inequalities and interchange the finite sums. A fixed path position $j$ occurs only for the seven possible starts $j-1,\ldots,j-7$, and only those belonging to $J$ contribute. Since each $\delta_j$ is nonnegative, the total is at most seven times the full excess sum. If each local demand is at most the same window sum, its maximum is also at most that sum. This proves both assertions. The finite-set summation and maximum rule have passed Lean checks.
\end{proof}

\begin{corollary}[Combined count and share charge]\label{cor:combined-budget}
Put $B=\sum_{j=0}^{m}b_j$ and $Q=\sum_{r\in J}D_r$. Let $C$ count a set of distinct forward occurrences of the six-coordinate pattern in Proposition~\ref{prop:three-square-bonus}. Then
\begin{equation}\label{eq:common-budget-charge}
168B+24Q+42C\le7G_{12}.
\end{equation}
\end{corollary}
\begin{proof}
Write $\Delta=\sum_j\delta_j$ and $\Sigma=\sum_{x\in S}\sigma_{12}(x)$. Proposition~\ref{prop:common-budget} gives $Q\le7\Delta$, and Corollary~\ref{cor:occurrence-share} gives $6C\le\Sigma$. Therefore
\[
168B+24Q+42C
\le168(B+\Delta)+7\Sigma
=7G_{12}.
\]
The final integer implication has also passed Lean. The excess and share terms use separate quantities; all excess demands share the same factor-seven budget.
\end{proof}

For example, the joint bound $\alpha_{r+3}+\alpha_{r+6}\ge12$ gives the demand
\[
\max\{0,12-b_{r+3}-b_{r+6}\}
\le\delta_{r+3}+\delta_{r+6}.
\]
The distance-three pair bounds give analogous deficits from nine or ten, and Proposition~\ref{prop:joint-singleton-excess} gives demands eleven or ten. Taking their maximum within a seven-centre window is always justified. Adding them would require a stronger accounting argument.

\subsection{What the enlarged finite model establishes}
The resulting computational model retains seven normalized directions and six count symbols, giving $34\cdot6^6=1\,586\,304$ states. A transition specifies eight directions and seven counts. It applies the radius-four catalogue to all represented subwindows and adds the identified proved exclusions and demands. Only the four completed cases of the six-centre all-four investigation are used; its unproved remaining cases are admitted. The transition weight is
\[
w=168b_{\mathrm{new}}+24D+42c,
\]
where $D$ is the maximum excess demand on the seven centres and $c\in\{0,1\}$ records one forward share occurrence ending at the new centre. This choice is motivated by~\eqref{eq:common-budget-charge}.

Independent integer verification of the saved graph gives the exact normalized minimum cycle mean
\begin{equation}\label{eq:six-count-mean}
\min_{\gamma}\frac{\sum_{e\in\gamma}w(e)}{168|\gamma|}=\frac{42}{11}.
\end{equation}
The minimum ranges over nonempty directed cycles of this finite graph. Two certificates establish the equality. First, an integer potential $\pi$ of range 8064 satisfies
\[
7056+\pi(v)\le11w(u,v)+\pi(u)
\]
on every one of the $4\,561\,226$ retained transitions. Summing around any cycle cancels the potential and proves the lower bound in~\eqref{eq:six-count-mean}. Second, the eleven-step cycle printed in Appendix~\ref{app:six-count-cycle} has appended-count sum 42 and $D=c=0$ at every step. It attains the bound. The arithmetic verification checks every edge of the saved graph; the full graph-generation and arbitrary-snake interpretation have not been checked in Lean.

The cycle shows why the incorporated corrections do not raise this model's limiting mean. It is not a snake construction: overlap of normalized directions and counts does not ensure one globally consistent selected-vertex set. Indeed, stronger radius-four seven-centre solver tests reject all eleven of its windows. Those tests have no replayed contradiction certificates here. They identify additional local exclusions to prove before the graph can be strengthened. The result is specific to this model and supplies no lower limit on what more complete local methods can achieve.

'''
replace(r'\section{What a stronger upper bound still requires}\label{sec:closure}',common+r'\section{Remaining requirements for a stronger bound}\label{sec:closure}')

# State the main line once and distinguish research reports from proof premises.
replace(r'''The established local inequalities can enter a global proof only through an accounting rule that prevents repeated use of the same contribution. Lemma~\ref{lem:share-packing}, the multiplicity bounds for count excess, and Corollary~\ref{cor:occurrence-share} supply such rules. A positive density of the relevant configurations, or a finite potential covering every allowed alternative, is still required.''',r'''The local theorems and common budget reduce the remaining upper-bound task to coverage: every permitted path sequence must receive enough total charge, including its initial and terminal positions. Eliminating a particular low-charge cycle is useful only if the revised model also controls the alternatives that replace it. The following targets specify the required strength of such an argument.''')
replace(r'''\section{Verification status and unresolved questions}\label{sec:verification}''',r'''\section{Verification scope and conclusions}\label{sec:verification}''')
replace(r'''The mathematical claims have different evidential scopes. Explicit transition sequences give existence statements only after all distinctness and adjacency conditions have been checked. A local exclusion requires a geometric interpretation of its input conditions as well as a sound contradiction certificate. A global upper bound additionally requires coverage of every relevant window and an aggregation argument with endpoint terms. The proofs of Theorems~\ref{thm:upper238} and~\ref{thm:upper236} follow this complete dependency chain.''',r'''The principal result is the interval $191\le a(9)\le236$. Its lower and upper bounds have different proof structures. The lower bound checks an explicit finite witness. The upper bound covers every snake through geometric normalization, interpreted local clauses, contradiction certificates, a complete finite potential check, and summation with endpoint terms. No restricted search result is a premise in this chain.

The empty-square approach has produced additional local theorems and a common overlap budget, without a smaller global bound. The enlarged graph computation proves an exact statement about its saved finite model. Its common-budget lemmas have three Lean dependency audits; its all-edge potential and attaining cycle have a separate integer check. The complete connection from that generated graph to arbitrary snakes remains a verification task. The eleven stronger solver exclusions remain numerical. These scopes prevent interpreting the graph cycle as a snake or interpreting its numerical rejection as a checked universal exclusion.''')
replace(r'''In particular, an unresolved solver run proves neither feasibility nor impossibility; a local forest proves feasibility only in its local model; and an exact mean of one saved state cycle is not a certificate of the minimum over all cycles.''',r'''In particular, an unresolved solver run proves neither feasibility nor impossibility, and a local forest proves feasibility only in its local model. The earlier diagnostic cycle values in Appendix~\ref{app:diagnostics} have no complete minimum-mean certificate. The six-count result in Section~\ref{sec:common-budget} has both an attaining cycle and an all-edge potential, so its stronger finite-model conclusion is justified within that stated scope.''')

# Add the actual cycle to the diagnostic appendix, before its older chronology.
analysis = json.loads((ROOT/'milestones/42-six-count-state-model/data/analysis.json').read_text())
rows = '\n'.join(f"{i} & $({','.join(map(str,r['directions']))})$ & $({','.join(map(str,r['counts']))})$\\\\" for i,r in enumerate(analysis['cycle']))
cycle = r'''\subsection{The exact six-count model certificate}\label{app:six-count-cycle}
The following eleven transitions form a closed cycle in the enlarged graph of Section~\ref{sec:common-budget}. At each transition, the first seven directions and first six counts specify the initial state; the last seven directions, renormalized, and last six counts specify the next state. These states agree successively, including the final-to-initial transition.
\begin{center}
\begin{tabular}{rll}
\toprule
Phase & Directions & Seven internal count symbols\\\midrule
'''+rows+r'''
\bottomrule
\end{tabular}
\end{center}
Every demand and share indicator is zero. The final count symbols sum to 42, so the total integer weight is $168\cdot42=7056$ and the normalized cycle mean is $42/11$. The accompanying potential verifies the matching lower bound on every retained graph edge. The certificate, graph specification, and verification receipt are archived together~\cite{sixcountarchive}.

Each row was also tested with its seven displayed counts as upper caps in the stronger radius-four acyclic window model. All eleven tests returned infeasibility. These numerical outcomes have no replayed refutations in this record, so they are not added to the proved exclusion family. They provide candidates for the next certificate work.

'''
replace(r'\subsection{Packing numerical window estimates}',cycle+r'\subsection{Packing numerical window estimates}')
replace(r'''The tables in this appendix are research diagnostics. A recorded local-witness value is an attainable value for one local assignment. A recorded lower-table value has the verification status stated with it. The mean of a saved cycle is checked by exact arithmetic, but this does not prove that it is the least mean of all cycles. None of the diagnostic means is used as a universal lower bound for snakes in this paper.''',r'''The first subsection records the exact finite-model result used in Section~\ref{sec:common-budget}. The remaining subsections retain earlier diagnostics in their order of development. In those earlier tables, a local-witness value is attainable by one local assignment, and a lower-table value retains the verification status stated with it. Checking the mean of a saved cycle alone does not prove a minimum over all cycles. None of these computations supplies a new universal bound on snake length.''')

# Repair an existing appendix-order error: the forest belongs with explicit witnesses.
forest_start = s.index(r'\subsection{A radius-three linear forest}')
forest_end = s.index(r'\begin{thebibliography}', forest_start)
forest = s[forest_start:forest_end]
s = s[:forest_start]+s[forest_end:]
replace(r'\section{Finite verification of the printed witnesses}\label{app:finite-check}',forest+'\n'+r'\section{Finite verification of the printed witnesses}\label{app:finite-check}')

# Replace stale forward-looking notebook narration throughout the appendices.
replacements = {
 'These are restrictions of this intermediate configuration and provide no global bound.':'These outcomes concern the specified intermediate configuration and provide no global bound.',
 'The constructive consequence is to enlarge the allowed vertices within cells. A useful next search permits vertices from the opposite base cycle, which can create cross-cell connections beyond the four shared connectors. The local census explains why retaining the original four-connector restriction is an unsuitable route to a 196-edge construction.':'The local census explains why this four-connector family cannot support the intended construction under its stated census premise. The expanded-cell experiments below permit vertices from the opposite base cycle and thereby allow additional cross-cell connections.',
 'The next constructive step is to vary the coordinate partition or replace connections across more cells simultaneously.':'The coordinate-face experiments below vary the released region to test broader replacements.',
 'The next search must allow changes to $F$ as well, since retaining the two-arm restriction already gave a solver exclusion at 196 edges.':'The restricted exclusion at 196 motivates the subsequent experiments that release vertices of $F$.',
 'The following investigation tests recombination with this common endpoint pair.':'This common endpoint pair is used in the recombination experiments below.',
 'The following investigation uses complete 191-edge donors without requiring their two endpoints to coincide with those of the recipient.':'The complete-donor experiments below allow internal donor anchors as well as donor endpoints.',
 'A subsequent construction direction is to obtain alternative 191-edge fillings and then change the free region, allowing the outside pattern to change between successive repairs.':'The alternative-filling experiments below test changes of selected set at equal or slightly smaller length before further growth.',
 r'These two exclusions were selected from periodic sequences admitted by a weaker diagnostic model. They eliminate those particular sequences. The modified model admits a replacement sequence at the same saved lower-table mean, so this result alone yields no improvement of Theorem~\ref{thm:upper238}. The computations and their precise scope are recorded in Appendix~\ref{app:diagnostics}.':r'These exclusions remove two periodic sequences admitted by an earlier diagnostic model. A replacement sequence has the same recorded lower-table mean, so those removals alone give no smaller global bound. Appendix~\ref{app:diagnostics} records the finite computations and their scope.',
 r'The following smaller finite models explain the intermediate bounds. They are retained separately from the direct proof of 238 in Section~\ref{sec:upper-proof}.':r'The following smaller finite models explain the intermediate bounds. The complete 238 argument is retained in Appendix~\ref{app:bound238}, and the direct proof of 236 is in Section~\ref{sec:upper-proof}.',
 r'The distinct-coordinate certificate remains under verification. These earlier certificate checks did not yet prove the geometric premise of Proposition~\ref{prop:conditional244}; the complete window proof in Section~\ref{sec:upper-proof} now establishes it.':r'At that stage the distinct-coordinate certificate and the complete geometric assembly were unfinished. Those earlier checks therefore did not establish the premise of Proposition~\ref{prop:conditional244}. The later complete window proof establishes it independently.',
 r'This conditional estimate is weaker than the unconditional bound 238 in Theorem~\ref{thm:upper238}.':r'This conditional estimate is weaker than the unconditional bound 236 in Theorem~\ref{thm:upper236}.',
}
for old,new in replacements.items(): replace(old,new)

# The forest is no longer incorrectly placed after the References ToC entry.
# Archive citation is pinned to the research commit supplied as an argument.
import sys
assert len(sys.argv) == 2 and re.fullmatch('[0-9a-f]{40}', sys.argv[1])
archive = sys.argv[1]
replace(r'\end{thebibliography}',r'''\bibitem{sixcountarchive}
I.~Hironaka, T.~Ma, and S.~Zhan. \emph{Six-count finite-state model: common excess budget, exact cycle mean, and local screens}. Archived research record, 24 October 2026.
\url{https://github.com/hironaka-iori/Snake-in-the-box-in-9/tree/'''+archive+r'''/milestones/42-six-count-state-model}.

\end{thebibliography}''')

# Every old mathematical statement is retained verbatim; proofs may move or clarify.
pattern = r'\\begin\{(theorem|lemma|proposition|corollary|conjecture|definition)\}.*?\\end\{\1\}'
statements = [m.group() for m in re.finditer(pattern, original, re.S)]
# One existing lemma statement now explicitly names its self-contained state definition.
for statement in statements:
    expected = statement.replace('on the same 44064 states', 'on the 44064 states just defined')
    assert expected in s, expected[:160]
oldlabels = set(re.findall(r'\\label\{([^}]+)\}', original))
labels = re.findall(r'\\label\{([^}]+)\}', s)
assert oldlabels <= set(labels) and len(labels) == len(set(labels))
refs = set(re.findall(r'\\(?:eqref|ref)\{([^}]+)\}',s))
assert refs <= set(labels), refs-set(labels)
assert s[:s.index(r'\begin{abstract}')] == original[:original.index(r'\begin{abstract}')]
assert r'.lean' not in s
HERE.joinpath('data').mkdir(parents=True,exist_ok=True)
EDITOR.write_text(s,encoding='utf-8')
PAPER.write_text(s,encoding='utf-8')
receipt = dict(prior_statements=len(statements), statements_preserved=True,
    statement_wording_clarifications=['Radius-four potential state reference made self-contained'],
    new_statements=2, old_labels=len(oldlabels), new_total_labels=len(labels),
    references_resolve=True, preamble_and_metadata_unchanged=True,
    before_sha256=hashlib.sha256(original.encode()).hexdigest(),
    after_sha256=hashlib.sha256(s.encode()).hexdigest(), source_archive=archive)
HERE.joinpath('data/rewrite-audit.json').write_text(json.dumps(receipt,indent=2)+'\n')
print(json.dumps(receipt,indent=2))
