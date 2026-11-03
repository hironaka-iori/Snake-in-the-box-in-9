"""Revise the existing editor source; preserve metadata and all appendices."""
from pathlib import Path
import hashlib,json,re,zipfile

HERE=Path(__file__).resolve().parents[1]
ROOT=HERE.parents[1]
EDITOR=Path('D:/Codex/2026-10-13/new-chat/outputs/snake9_research.tex')
PAPER=ROOT/'paper/snake9_research.tex'
for directory in ['data','audit','logs']:(HERE/directory).mkdir(parents=True,exist_ok=True)
raw=EDITOR.read_bytes()
assert raw==PAPER.read_bytes()
assert hashlib.sha256(raw).hexdigest()=='f649b4dfc0b3f11958105517d00f567db591517e5a3434e1dfad3cfc212b3429'
backup=HERE/'data/paper-before.zip'
assert not backup.exists(),'Never overwrite the preserved prior source.'
with zipfile.ZipFile(backup,'w',zipfile.ZIP_DEFLATED) as archive:archive.writestr('snake9_research.tex',raw)
old=raw.decode('utf-8').replace('\r\n','\n');text=old
def replace(before,after):
    global text
    assert text.count(before)==1,before[:120]
    text=text.replace(before,after)
def insert(marker,content):replace(marker,content+'\n\n'+marker)

abstract=r'''Let $a(9)$ be the maximum edge length of an induced path in the nine-dimensional binary hypercube. An explicit construction and an archived contributor proof give $191\le a(9)\le235$; a complete independent rebuild of the upper-bound proof remains pending. The square census gives $T+2s_0+35(m+1)=9214$, and the six-centre count estimate yields $39m+2s_0\le9200$. Integer shares retain the empty-square contribution. Local share inequalities, overlap accounting and finite graph coverage give a total-weight bound $W+4200m\le1098960$. Subject to the remaining reference refutations and complete potential certificate, slope 483 and range 551 recover 235. Five additional local shares would permit slope 496 and range 602, giving 234. Twelve of the 1378 reference entries are now discharged. Further checked restrictions constrain three internal singleton counts and, on direction pattern $012314$, force the outer four counts to sum to at least 19 when the middle count is at most two. A shared excess budget incorporates such sum inequalities without repeated counting. Experiments assuming additional unproved count inequalities raise the first finite-graph mean to $6309/13$, while the stronger-share mean remains 496. Their integer comparisons remain 235 and 234. Surviving cycles show why stronger bounds confined to six distinct directions cannot improve these means. The exact optimum and the conjecture 196 remain unresolved.'''
replace(text.split('\\begin{abstract}\n',1)[1].split('\n\\end{abstract}',1)[0],abstract)
replace('It then derives the upper-bound implications, identifies the least sufficient pending floors in the fixed model, and explains the limits of changing the potential parameters.', 'It then derives the upper-bound implications, identifies the least sufficient pending floors in the fixed model, and explains the limits of changing the potential parameters. Section~\\ref{sec:sum-refinements} examines additional count-sum restrictions and the replacement cycles that limit their effect.')
replace(r'Graph interpretation and total charge & Complete coverage and all weight components are checked. The actual-walk implication retains the exact 1378-key reference premise.\\',r'Graph interpretation and total charge & Complete coverage and all baseline weight components are checked. Twelve of the 1378 reference entries are discharged; 1366 remain.\\'+'\n'+r'New local count restrictions & Checked three-count exclusions and a four-count sum bound. Additional sum hypotheses give conditional finite comparisons only.\\')

insert(r'\section{Deriving empty-square bounds from local geometry}',r'''\subsection{Restrictions using fewer count hypotheses}\label{sec:recent-counts}
The following statements retain only the counts needed for their proofs.
Every direction word begins at $x_r$ and must fit inside the snake. Distinct
digits denote distinct coordinate directions, up to relabelling.

\begin{proposition}[Further short-window restrictions]\label{prop:recent-counts}
The indicated alternatives hold for every matching snake segment:
\[
\begin{array}{c|l}
\text{directions}&\text{conclusion}\\\hline
012304&\alpha_{r+1}\ge3\ \text{or}\ \alpha_{r+4}\ge3\ \text{or}\ \alpha_{r+5}\ge4\\
01234&\alpha_{r+1}\ge2\ \text{or}\ \alpha_{r+2}\ge6\ \text{or}\ \alpha_{r+4}\ge3\\
012340&\alpha_{r+2}\ge4\ \text{or}\ \alpha_{r+3}\ge3\ \text{or}\ \alpha_{r+4}\ge6.
\end{array}
\]
For $012340$, the five internal counts also cannot equal $(5,5,2,4,5)$.
Every assertion holds with the directions and counts jointly reversed.
\end{proposition}
\begin{proof}[Computer-assisted proof]
Normalize the segment and impose the contrary upper bounds in the necessary
radius-four model. The first row requires only caps two, two and three at
positions one, four and five. The second requires caps one, five and two at
positions one, two and four. Other counts retain their full internal range.
The retained contradictions use respectively 120 and 441 clauses, with 75
and 270 deductions. Their clause interpretations and refutations are checked.
The second row's unrestricted third count is essential to the stated scope.

For the third row, impose caps three, two and five at positions two, three
and four, leaving the first and fifth counts unrestricted. Thirteen added
cycle exclusions follow from Lemma~\ref{lem:subset-low-degree}. The retained
2040-clause contradiction has 11711 deductions. The separate exact tuple
$(5,5,2,4,5)$ has a 1664-clause contradiction with 2007 deductions.
Its second count is five, so the third row alone does not exclude it.

Each hypothetical snake supplies the selected vertices, endpoint indicators
and actual missing-corner counts satisfying the necessary clauses. The
checked contradictions exclude these assignments. Coordinate transport
preserves all counts; reversing the segment reverses their order. The
actual-snake deductions and their uses in both graph orientations have
passed Lean~\cite{recoveryarchive,criticalcountarchive}. These statements
have no collective reference-catalogue premise.
\end{proof}

\begin{theorem}[Four-count sum under a small middle count]\label{thm:outer-four-sum}
Suppose $r+6\le m$ and the six transitions beginning at $x_r$ have pattern
$012314$. Then
\[
\alpha_{r+3}\le2
\quad\Longrightarrow\quad
\alpha_{r+1}+\alpha_{r+2}+\alpha_{r+4}+\alpha_{r+5}\ge19.
\]
The statement also holds with the segment reversed.
\end{theorem}
\begin{proof}[Computer-assisted proof]
Translate $x_r$ to zero and relabel coordinates. The selected segment is
$(0,1,3,7,15,13,29)$. Suppose the middle count is at most two and the four
outer counts sum to at most eighteen. At each outer centre, list the 21
opposite corners whose coordinate pairs avoid its two path directions.
By Lemma~\ref{lem:window-missing-corners}, its singleton count equals the
number of absent entries in that list.

Concatenating the four lists gives 84 occurrences involving 70 distinct
corners. Repeated corners retain their multiplicities because they
contribute to separate singleton counts. Sorting the occurrences preserves
their sum. A threshold counter on this list therefore represents exactly
the assumed four-count upper bound.

Together with the selected segment, degree, endpoint and cycle conditions,
these assumptions have a retained contradiction with 3306 clauses, 7020
deductions and 367588 antecedent references. The counter interpretation,
clause validity, full contradiction and transfer to arbitrary coordinate
labels have passed Lean~\cite{sumbudgetarchive}. Thus the hypothetical
upper sum eighteen is impossible. Integrality proves the lower bound
nineteen. Reversal preserves the selected set and exchanges the four outer
positions among themselves. No collective catalogue premise enters this
theorem. Sharpness for complete snakes remains unresolved.
\end{proof}''')

insert(r'\subsection{The earlier seven-centre model}',r'''\subsection{A common budget for four-count and five-count restrictions}\label{sec:four-five-budget}
A lower bound on actual singleton counts can force excess above their
truncated values. For any set of positions $I$ and valid bound
$\sum_{i\in I}\alpha_i\ge L$,
\[
\max\left\{0,L-\sum_{i\in I}b_i\right\}
\le\sum_{i\in I}\delta_i.
\]
This follows from $\alpha_i=b_i+\delta_i$ and nonnegative excess.
Different bounds can use the same excess, so their charges require one
common capacity.

\begin{proposition}[Shared five-position excess budget]\label{prop:four-five-budget}
Let $a,c\ge0$ be integers with $4a+c\le120$. In a nine-transition window
beginning at $x_r$, consider the final five internal positions $r+4$ through
$r+8$. Suppose $q_r\ge0$ is at most
\[
a(\delta_{r+4}+\delta_{r+5}+\delta_{r+7}+\delta_{r+8})
+c\delta_{r+6}.
\]
For any set of distinct fitting starts,
\[
\sum_r q_r\le120\sum_{i=0}^{m}\delta_i.
\]
The maximum of the following applicable contributions is a permissible
choice of $q_r$: coefficient $a$ times a deficit on the four outer
positions; coefficient $a$ times a deficit on the outer pair; and
coefficient $\min\{a,c\}$ times a deficit on all five positions.
Each deficit uses a valid lower bound on the corresponding actual counts.
\end{proposition}
\begin{proof}
The preceding deficit inequality bounds each contribution by the displayed
weighted excess. For the outer pair, nonnegativity permits the other two
outer excesses to be included. For all five positions, the coefficient
$\min\{a,c\}$ is at most each assigned coefficient. Their maximum is
therefore bounded by the same expression.

For each fixed offset, distinct starts give distinct path positions.
Summing over starts counts any excess at most four times with coefficient
$a$ and once with coefficient $c$. The resulting total is at most
$(4a+c)\sum_i\delta_i\le120\sum_i\delta_i$.
The deficit inequalities, maximum rule and finite summation have passed
Lean under their stated local lower-bound premises
~\cite{sumbudgetarchive,pairbudgetarchive}.
\end{proof}

This budget preserves the boundary estimate. Let $L_r$ be a valid share
bound on the same five positions and now use weights
$120b_{r+8}+L_r+q_r$. Clipping at six preserves each omitted adjacent-pair
lower bound four, both endpoint lower bounds four and the remaining lower
bound one. Thus the omitted truncated counts sum to at least 21. The total
base count is at most $120(\sum_i b_i-21)$, the extra charge is at most
$120\sum_i\delta_i$, and the shares contribute at most $5\Sigma$.
Adding gives $W+2520\le5G_{12}$ and hence $W+4200m\le1098960$.
The clipped boundary and arithmetic have passed Lean. For any concrete
graph refinement, the validity and placement of every chosen local rule
still have to be connected to these premises.''')

replace('The new proof chain assumes refutations only for the exact 1378-key reference union.', 'The new proof chain uses the exact 1378-key reference union. Twelve entries now have checked refutations, leaving 1366 outstanding.')
replace('The remaining assumption is that each\nof its 1378 local necessary-condition systems has a refutation.', 'Twelve of its 1378 local necessary-condition systems now have checked\nrefutations. The remaining assumption concerns the other 1366 systems;\nthe union itself and its indices are unchanged.')
replace('keys and prove the implication; they do not supply their refutations.', 'keys and prove the implication. Subsequent recovery supplies twelve\nrefutations, with checked weakening of bounds and an equivalence between\nthe full premise and the remaining 1366 entries~\\cite{recoveryarchive}.')
replace('that tradeoff for each of the three current weighted graphs.', 'that tradeoff for each of the three weighted graphs specified below.')
replace('The three current certificates have the following open-walk data.', 'The three certificates for those specified profiles have the following open-walk data.')
replace('The hypothesis concerns the current graph and the current global budget.', 'The hypothesis concerns the baseline graph and its stated global budget.')
replace('The completed-share graph has a minimum-mean cycle on which every', 'The baseline graph with completed share floors has a minimum-mean cycle on which every')
replace('The graph considered here contains\nevery bounded full key', 'The baseline graph considered here contains\nevery bounded full key')

insert(r'\section{Remaining requirements for a stronger bound}',r'''\section{Further count-sum restrictions and their limits}\label{sec:sum-refinements}
The preceding graph and its proof obligations remain fixed. The experiments
in this section add count restrictions to copies of that graph. Several
restrictions remain hypotheses, even when the share floors are already
proved. A completed-floor label therefore identifies the share inputs;
it does not certify the resulting refined comparison for arbitrary snakes.

\subsection{Local hypotheses and their verification status}
The following table gives the ten sum rules used in the final experiment.
Positions are offsets from the start $x_r$ of the listed six-transition
word. An empty condition means that only the direction word is assumed.
Bounds on an unlisted count are absent.
\begin{center}\small
\begin{tabular}{c l c r}
\toprule
Directions & Condition & Positions summed & Lower bound\\\midrule
$012340$ & $\alpha_{r+3}\le2$ & $1,2,4,5$ & 22\\
$012340$ & $\alpha_{r+3}\le3$ & $1,2,4,5$ & 19\\
$012340$ & $\alpha_{r+3}\le5$ & $1,2,4,5$ & 18\\
$012340$ & & $1,2,4,5$ & 17\\
$012034$ & & $1,2,3,4,5$ & 20\\
$012031$ & $\alpha_{r+3}\le5$ & $1,2,4,5$ & 15\\
$012314$ & $\alpha_{r+3}\le2$ & $1,2,4,5$ & 19\\
$012034$ & $(\alpha_{r+2},\alpha_{r+3},\alpha_{r+4})\le(5,4,5)$ & $1,5$ & 9\\
$012310$ & & $1,2,3,4,5$ & 19\\
$012345$ & & $1,2,3,4,5$ & 22\\\bottomrule
\end{tabular}
\end{center}
The $012314$ row is Theorem~\ref{thm:outer-four-sum}. The other rows remain
unproved for arbitrary snakes in the current Lean development. For
$012340$ with middle count at most two, a complete independent native
refutation supports 22; its concrete interpretation and Lean replay are
unfinished. For $012310$, both an independent native refutation and the
concrete count interpretation are checked, while its complete Lean
contradiction and final actual-snake deduction remain pending. The selected
proof uses 5067 of its 5114 input clauses, 287753 deductions and 16816989 antecedent
references. Its five counters retain 105 corner occurrences involving 84
distinct corners. Partial replay does not establish the row
~\cite{criticalcountarchive,totalcountarchive}.

The remaining proposed restrictions have native solver exclusions with
incomplete contradiction certificates. In particular, two proof-generation
attempts for the outer-pair row reached their time limits. A checked local
forest with counts $(6,5,4,5,3)$ attains its proposed sum nine, so the same
relaxed local conditions cannot force ten. Such forests have multiple
components and relaxed boundary conditions; they establish no complete
snake or sharpness for complete snakes~\cite{pairbudgetarchive}.

For six distinct directions, a stronger candidate is
\[
\sum_{j=1}^{5}\alpha_{r+j}\ge23.
\]
The native search rejects a sum at most 22 after five individually validated
cycle exclusions. Its negative certificate still requires independent
replay and Lean checking. An independently checked local forest has counts
$(6,3,6,2,6)$, attaining 23. Its 105 selected vertices have six components
of sizes $43,27,24,9,1,1$ and two fully represented endpoints. This gives
a local upper limit on a possible improvement under those relaxed
conditions; a complete-snake equality example is unknown. The weaker
last row of the table suffices for the finite comparison below
~\cite{totalcountarchive}.

\subsection{Comparison of both share profiles}
For the first nine rules, and then all ten, use the shared budget of
Proposition~\ref{prop:four-five-budget} with $a=c=24$. Apply all valid
exclusions in both orientations and placements. Extra charge uses only
the final five internal positions. A symbol below six is exact; six
retains its interval $[6,21]$. A sum below the proposed bound therefore
rejects an edge only when the participating counts are exact. Otherwise
the deficit is charged to their excess, subject to the common budget.

Every listed finite comparison has an integer potential checked against
all retained full-key edges and a saved cycle attaining the indicated
mean. The table gives the unscaled means and potential ranges. The
fractional entries use a common denominator to obtain integer certificates.
\begin{center}\small
\begin{tabular}{l c c c}
\toprule
Additional sum rules & Completed-floor mean & Range & Integer comparison\\\midrule
First seven rows & $484$ & $557$ & 235\\
First eight rows & $484$ & $557$ & 235\\
First nine rows & $2424/5$ & $2881/5$ & 235\\
All ten rows & $6309/13$ & $7656/13$ & 235\\\bottomrule
\end{tabular}
\end{center}
In all four experiments the conditional-share profile has mean 496,
recorded range 602 and integer comparison 234. The final exact fractions
from~\eqref{eq:improved-potential} are
\[
\frac{1098960\cdot13+8\cdot6309+7656}{4200\cdot13+6309}
=\frac{4781536}{20303},\qquad
\frac{1098960+8\cdot496+602}{4200+496}
=\frac{551765}{2348}.
\]
These are conditional finite-graph calculations. The outstanding local
rules, their concrete graph integration, reference refutations and complete
Lean potential certificates prevent promoting them to new unconditional
snake bounds~\cite{sumbudgetarchive,pairbudgetarchive,totalcountarchive}.

The final attaining cycles have 26 and six edges. Neither contains a
$012345$ window at either tested placement, covering 64 placements in
total. Raising only the last lower bound from 22 to 23 therefore leaves
both cycles and all their weights unchanged. Every surviving edge has
nondecreasing weight, and an edge deletion cannot invalidate an earlier
potential inequality on the remaining edges. The old potentials remain
valid, while the unchanged cycles attain the old means. Consequently the
exact means remain $6309/13$ and 496, and the displayed ranges remain
valid. This argument makes no claim that these ranges are minimal, and
it does not count the newly deleted edges. Any further strengthening
confined to this absent direction shape has the same limitation.

\subsection{What an integer improvement requires}
The comparison~\eqref{eq:improved-potential} excludes length 235 exactly when
$227p>111960d+R$, and excludes length 234 exactly when
\[
226p>116160d+R.
\]
Both equivalences follow by substituting the respective length and moving
terms; they have passed Lean~\cite{totalcountarchive}. With $d>0$ and
$R\ge0$, even zero range requires the respective slopes to exceed
\[
\frac{111960}{227}\quad\text{and}\quad\frac{58080}{113}.
\]
The final completed-floor mean is below the first threshold, since
\[
111960\cdot13-227\cdot6309=23337>0.
\]
The conditional-share mean is below the second, since
$116160-226\cdot496=4064>0$. Hence range reduction alone cannot improve
the two integer comparisons. Further progress must affect a surviving
cycle, change the allowed walks or improve the global accounting. The
saved cycles identify concrete windows for that next test; they are
sequences in the comparison graph and supply no snake constructions.''')

replace('\\item Supply refutations for every local system in the exact union of 1378\nreference keys.', '\\item Supply the remaining 1366 refutations in the exact union of 1378\nreference keys. Twelve entries have been discharged, with the equivalence\nto the reduced premise checked.')
replace('The unsaturated\ncycle rules out improvements confined to count symbol six.', 'The baseline unsaturated\ncycle rules out such improvements while that graph is retained. The\nrefinements in Section~\\ref{sec:sum-refinements} replace this cycle; their\nnew attaining cycles avoid six-distinct-direction windows and still leave\nthe integer comparisons unchanged.')
replace('The 1378 reference refutations also\nremain to be supplied in the current checking environment.', 'Of the 1378 reference entries, twelve now have checked refutations in the\ncurrent environment; the remaining 1366 form the reduced premise.')
replace('No construction above 191 or matching optimality theorem has been obtained.', 'The new local restrictions and four-count theorem are checked for actual\nsnakes. The broader sum family has mixed verification status, as detailed in\nSection~\\ref{sec:sum-refinements}. Its improved finite mean does not lower\nthe maintained interval.\n\nNo construction above 191 or matching optimality theorem has been obtained.')

commit='5aabaead83018d1f39743ac4b990eebeb7ede2c0'
entries=[('recoveryarchive','Recovered reference refutations and relaxed short-window restrictions','107--109','109-relaxed-graph-test'),('criticalcountarchive','Short-window count exclusions and proposed outer sums','110--111','111-critical-count-intervals'),('sumbudgetarchive','An actual four-count theorem and shared excess accounting','112','112-critical-sum-refinement'),('pairbudgetarchive','Conditional outer-pair restrictions and their shared budget','113','113-all-four-sum-pressure'),('totalcountarchive','Five-count certificates, distinct-direction candidates and finite comparison limits','114--115','115-total-count-certificate')]
items=[]
for key,title,rounds,path in entries:
    items.append(r'\bibitem{'+key+'}\n'+r'I.~Hironaka, T.~Ma, and S.~Zhan. \emph{'+title+'}. Research milestones '+rounds+r', included in pinned revision \texttt{5aabaead}, 3 November 2026.'+'\n'+r'\url{https://github.com/hironaka-iori/Snake-in-the-box-in-9/tree/'+commit+'/milestones/'+path+'}.')
insert(r'\end{thebibliography}','\n\n'.join(items))

assert old.split(r'\begin{abstract}')[0]==text.split(r'\begin{abstract}')[0]
refmarker=r'\clearpage'+'\n'+r'\addcontentsline{toc}{section}{References}'
assert old.split(r'\appendix',1)[1].split(refmarker,1)[0]==text.split(r'\appendix',1)[1].split(refmarker,1)[0]
assert text.count(r'\begin{definition}')==1
newraw=text.replace('\n','\r\n').encode('utf-8')
EDITOR.write_bytes(newraw);PAPER.write_bytes(newraw)
revision={'status':'REVISED_SOURCE_PENDING_VERIFICATION','prior_sha256':hashlib.sha256(raw).hexdigest(),'paper_sha256':hashlib.sha256(newraw).hexdigest(),'new_definitions':0,'named_definitions':1,'added_statement_labels':['prop:recent-counts','thm:outer-four-sum','prop:four-five-budget'],'changed_prior_statement_labels':[],'author_and_hypersetup_preserved':True,'all_appendices_preserved':True,'source_commit':commit}
(HERE/'data/revision.json').write_text(json.dumps(revision,indent=2)+'\n',encoding='utf-8')
print(json.dumps(revision,indent=2))
