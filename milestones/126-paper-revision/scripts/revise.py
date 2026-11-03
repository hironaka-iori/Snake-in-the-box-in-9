"""Revise the open manuscript from the exact saved baseline, without new definitions."""
from pathlib import Path
import hashlib,json,re,zipfile
H=Path(__file__).resolve().parents[1]; R=H.parents[1]
E=Path('D:/Codex/2026-10-13/new-chat/outputs/snake9_research.tex')
P=R/'paper/snake9_research.tex'
with zipfile.ZipFile(H/'data/paper-before.zip') as z: raw=z.read('snake9_research.tex')
assert hashlib.sha256(raw).hexdigest()=='5e62b785321b8b624338e484560f3ac16d048699c841deeccc69573fd13be72f'
assert E.read_bytes()==P.read_bytes()==raw
old=raw.decode('utf-8').replace('\r\n','\n'); text=old
def replace(a,b):
 global text
 assert text.count(a)==1,(text.count(a),a[:100])
 text=text.replace(a,b)
def insert(marker,s): replace(marker,s+'\n\n'+marker)
abstract=r'''Let $a(9)$ denote the maximum edge length of an induced path in the nine-dimensional binary hypercube. An explicit construction and an archived contributor proof give $191\le a(9)\le235$; a complete independent rebuild of the upper-bound proof remains pending. Writing $\alpha_i$ for the singleton-square count at path vertex $i$, $T=\sum_i\alpha_i$, and $s_0$ for the number of empty squares, the exact identity is $T+2s_0+35(m+1)=9214$. Direct summation shows that a universal lower bound of 25 on six consecutive internal counts would imply $a(9)\le234$; a bound of 26 would imply $a(9)\le233$. A weaker sufficient condition bounds the combined shortfall below 25 over 39 disjoint groups by $28+2s_0$. These implications are checked, while their additional hypotheses remain unresolved. The six-count bound 25 is proved for direction pattern $0123041$ and its reversal. A sharp pair-count theorem and a restriction on possible $0120324$ counterexamples supply further local constraints. Separately, empty-square shares and finite comparison graphs yield conditional bounds and identify surviving cycles that limit the tested refinements. Twenty of 1378 reference entries are discharged; the remaining refutations, complete potential certificate and five additional share bounds retain their stated roles. The optimum and the numerical conjecture 196 remain unresolved.'''
replace(text.split('\\begin{abstract}\n',1)[1].split('\n\\end{abstract}',1)[0],abstract)
replace('The argument proceeds from local geometry to global accounting.',r'The argument proceeds from local geometry to global accounting. Section~\ref{sec:six-direct} first gives direct six-count criteria for 234 and 233, retaining the empty-square term. These criteria require no finite comparison graph.')
replace(r'Graph interpretation and total charge & Complete coverage and all baseline weight components are checked. Twelve of the 1378 reference entries are discharged; 1366 remain.\\',r'Graph interpretation and total charge & Complete coverage and all baseline weight components are checked. Twenty of 1378 reference entries are discharged; 1358 remain.\\')
replace(r'New local count restrictions & Checked three-count exclusions and a four-count sum bound. Additional sum hypotheses give conditional finite comparisons only.\\',r'Direct six-count criteria & Universal floors 25 and 26 would give 234 and 233. The shortfall criterion retains $2s_0$. These extra premises remain unresolved.\\'+'\n'+r'New local count restrictions & The six-count floor 25 is proved for $0123041$. The $012032$ pair bound eight is sharp; $0120324$ has a checked necessary interval restriction.\\')

insert(r'\section{Sharp restrictions on two singleton counts}',r'''\section{Direct six-count bounds with empty squares retained}\label{sec:six-direct}
The square identity and the endpoint estimates already give useful sufficient
conditions for a stronger bound. Throughout this section, a six-count lower
bound means
\[
\sum_{j=1}^{6}\alpha_{r+j}\ge L\qquad(r\ge0,\ r+7\le m),
\]
for every fitting group of six consecutive internal vertices of the snake.

\begin{proposition}[Conditional bounds from six consecutive counts]\label{prop:six-direct}
Each row gives a sufficient condition for the indicated upper bound on the
length of a snake. The six-count bound is assumed at every fitting group.
The empty-square condition is required only at the lengths specified.
\begin{center}
\begin{tabular}{c l c}
\toprule
Six-count bound & Empty-square condition & Conclusion\\\midrule
25 & None & $m\le234$\\
26 & None & $m\le233$\\
24 & $s_0\ge6$ if $m\ge235$ & $m\le234$\\
23 & $s_0\ge25$ if $m\ge235$ & $m\le234$\\
25 & $s_0\ge14$ if $m\ge234$ & $m\le233$\\\bottomrule
\end{tabular}
\end{center}
\end{proposition}
\begin{proof}
For $m\ge229$, take 38 disjoint groups occupying internal positions 1 through
228. The other $m-229$ internal counts are at least one, and the two endpoint
counts total at least eight. Hence
\[
T\ge38L+(m-229)+8.
\]
For $L=25$ and $L=26$, respectively, substitution into the square identity gives
\[
36m+764+2s_0\le9214,\qquad36m+802+2s_0\le9214.
\]
These exclude $m\ge235$ and $m\ge234$. If $L=25$ and $m\ge234$, the first
inequality also gives $2s_0\le26$, contradicting $s_0\ge14$.

For $m\ge235$, use 39 groups occupying internal positions 1 through 234.
Then $T\ge39L+(m-235)+8$. The choices $L=24$ and $L=23$ yield
$T\ge m+709$ and $T\ge m+670$. At $m=235$, adding $35(m+1)$ and the
respective lower bound on $2s_0$ gives 9216 and 9215, each exceeding 9214.
The left sides increase with $m$, so larger lengths are also excluded.
Lengths below each contradiction threshold already satisfy the conclusion.
The deductions and their application to actual snakes have passed
Lean~\cite{uniformsixarchive,criticalsixarchive}.
\end{proof}
None of the universal six-count hypotheses or additional empty-square
hypotheses in this proposition has been proved. The implications therefore
give precise targets; they do not lower the maintained interval by themselves.

\begin{theorem}[Necessary total shortfall at length 235]\label{thm:six-shortfall}
Every snake with $m\ge235$ satisfies
\begin{equation}\label{eq:six-shortfall}
\sum_{b=0}^{38}\max\left\{0,25-\sum_{j=1}^{6}\alpha_{6b+j}\right\}
\ge29+2s_0.
\end{equation}
Consequently, an upper bound of $28+2s_0$ on this same sum for every snake
with $m\ge235$ would imply $a(9)\le234$.
\end{theorem}
\begin{proof}
Each group sum plus its shortfall below 25 is at least 25. Positivity at
the remaining internal vertices and the endpoint estimates give
\[
T+\sum_{b=0}^{38}\max\left\{0,25-\sum_{j=1}^{6}\alpha_{6b+j}\right\}
\ge39\cdot25+(m-235)+8=m+748.
\]
Substitute $T=9179-35m-2s_0$. The shortfall is at least
$36m-8431+2s_0\ge29+2s_0$. This contradicts the proposed upper bound.
Both statements for arbitrary snakes have passed Lean~\cite{criticalsixarchive}.
\end{proof}
For example, the sufficient upper bound holds if all 39 group sums are at
least 23 and at most 14 are below 25: the shortfall is then at most 28.
Neither this floor nor the frequency restriction is established. The endpoint
occurrence bound discussed later concerns different events; applying it here
would require a new geometric implication.

\begin{theorem}[A proved six-count window]\label{thm:six-0123041}
Suppose $r+7\le m$ and the seven transitions beginning at $x_r$ have canonical
pattern $0123041$. Then
\[
\sum_{j=1}^{6}\alpha_{r+j}\ge25.
\]
The conclusion also holds when the segment is reversed.
\end{theorem}
\begin{proof}[Computer-assisted proof]
Translate and relabel the window to $(0,1,3,7,15,14,30,28)$. At each of its
six internal vertices, Lemma~\ref{lem:window-missing-corners} expresses the
singleton count as the number of absent opposite corners among 21 entries.
Across the six lists there are 126 occurrences and 105 distinct corners:
85 occur once, 19 twice and one three times. Preserve every occurrence when
counting the sum, including repetitions at different centres.

Assume the sum is at most 24. Selection of an actual snake, its endpoint
indicators and these missing-corner counts satisfies the corresponding
necessary conditions on the complete cube. A retained contradiction uses
3649 input clauses and 5746 deductions. Its count interpretation, complete
replay and transfer to arbitrary coordinate labels have passed Lean. No
additional cycle exclusion is needed. Thus the contrary sum is impossible;
integrality gives 25. Reversal preserves the sum and the induced-path
conditions~\cite{uniformsixarchive}.
\end{proof}

There are 34 canonical induced seven-transition words, forming 21 classes
under reversal. The preceding theorem closes one class. Full-cube searches
returned negative results for 19 classes, including this one; the other
18 still require complete checked deductions. The classes $0120310$ and
$0120324$ remain unresolved. The saved bank of 134 paths has minimum
six-count sum 31, which supplies no universal lower bound. Earlier checks
of runs with every count equal to four do not prove a lower bound on the
sum. A universal theorem also requires an audited connection between the
complete direction classification and every local proof~\cite{uniformsixarchive}.''')

replace(r'\section{The current finite comparison graph and its interpretation}',r'\section{A finite comparison graph and its interpretation}')
replace('The earlier complete models and their replacement cycles are retained in Appendix~\\ref{app:earlier-long-models}. The present model uses recorded proofs for its local rules, with stronger share targets kept separate. This distinction permits the conditional and completed-proof tracks to be compared on the same state space.',r'This section specifies the baseline finite graph, proves how a snake determines its state sequence, and accounts for its edge weights. The reference-catalogue premise and the complete potential certificate are stated explicitly. Later refinements are compared separately in Section~\ref{sec:sum-refinements}, retaining each additional local hypothesis. Earlier models and their replacement cycles are retained in Appendix~\ref{app:earlier-long-models}.')
replace('Twelve entries now have checked refutations, leaving 1366 outstanding.',r'Twenty entries now have checked refutations, leaving 1358 outstanding~\cite{pair012032archive}.')
replace('Twelve of its 1378 local necessary-condition systems now have checked\nrefutations. The remaining assumption concerns the other 1366 systems;', 'Twenty of its 1378 local necessary-condition systems now have checked\nrefutations. The remaining assumption concerns the other 1358 systems;')
replace('Subsequent recovery supplies twelve\nrefutations, with checked weakening of bounds and an equivalence between\nthe full premise and the remaining 1366 entries~\\cite{recoveryarchive}.','Subsequent recovery supplies twenty\nrefutations, with checked weakening of bounds and an equivalence between\nthe full premise and the remaining 1358 entries~\\cite{recoveryarchive,pair012032archive}.')
replace('Supply the remaining 1366 refutations in the exact union of 1378\nreference keys. Twelve entries have been discharged,','Supply the remaining 1358 refutations in the exact union of 1378\nreference keys. Twenty entries have been discharged,')
replace('Of the 1378 reference entries, twelve now have checked refutations in the\ncurrent environment; the remaining 1366 form the reduced premise.','Of the 1378 reference entries, twenty now have checked refutations in the\ncurrent environment; the remaining 1358 form the reduced premise.')
replace('Twenty-one omitted singleton counts','Boundary contribution of twenty-one')
replace(r'Put $z_j=24\delta_j+\sigma_{12}(x_j)$, and let $R_i$ be any valid lower bound for $\sum_{j=i+1}^{i+7}z_j$.',r'Let $R_i$ be any valid lower bound for $\sum_{j=i+1}^{i+7}(24\delta_j+\sigma_{12}(x_j))$.')
replace(r'give $24D_i+L_i\le\sum z_j$.',r'give $24D_i+L_i\le\sum_j(24\delta_j+\sigma_{12}(x_j))$ over the same window.')

# Additional reviewed local results, refined graph comparisons and appendix data
# are read from fixed text fragments written before this revision is applied.
insert(r'\section{Deriving empty-square bounds from local geometry}',(H/'data/local-results.tex.txt').read_text(encoding='utf-8'))
insert(r'\subsection{What an integer improvement requires}',(H/'data/refined-comparisons.tex.txt').read_text(encoding='utf-8'))
replace('The following table gives the ten sum rules used in the final experiment.','The following table gives the ten sum rules used in the first comparison below.')
replace('The final completed-floor mean is below the first threshold, since', 'The ten-rule completed-floor mean is below the first threshold, since')
replace('The\nrefinements in Section~\\ref{sec:sum-refinements} replace this cycle; their\nnew attaining cycles avoid six-distinct-direction windows and still leave\nthe integer comparisons unchanged.',r'The refinements in Section~\ref{sec:sum-refinements} replace this cycle; the latest attaining cycles avoid all three seven-transition shapes tested there and still leave the integer comparisons unchanged.')
replace(r'\section{Remaining requirements for a stronger bound}\label{sec:closure}'+'\n'+r'The maintained interval is $191\le a(9)\le235$. The newer argument has',r'\section{Remaining requirements for a stronger bound}\label{sec:closure}'+'\n'+r'The maintained interval is $191\le a(9)\le235$. The direct criteria in Section~\ref{sec:six-direct} require a universal six-count floor, a bound on total shortfall, or one of the stated joint count and empty-square assumptions. The proved $0123041$ class and the necessary $0120324$ intervals do not discharge these premises. For the separate share argument, the newer proof has')
replace('The new local restrictions and four-count theorem are checked for actual\nsnakes. The broader sum family has mixed verification status, as detailed in\nSection~\\ref{sec:sum-refinements}. Its improved finite mean does not lower\nthe maintained interval.',r'''The pair bound for $012032$, the six-count bound for $0123041$, and the
necessary intervals for low-total $0120324$ windows are checked for actual
snakes. The direct shortfall theorem retains empty squares and requires no
reference union or graph potential. Its sufficient upper bound on shortfall
is unresolved. The broader sum family has mixed verification status, as
detailed in Section~\ref{sec:sum-refinements}; neither its finite comparison
nor the incomplete endpoint-equality argument lowers the maintained interval.''')
insert(r'\clearpage'+'\n'+r'\addcontentsline{toc}{section}{References}',(H/'data/new-witnesses.tex.txt').read_text(encoding='utf-8'))
insert(r'\end{thebibliography}',(H/'data/new-references.tex.txt').read_text(encoding='utf-8'))
assert '.lean' not in text
assert old.split(r'\begin{abstract}')[0]==text.split(r'\begin{abstract}')[0]
assert text.count(r'\begin{definition}')==old.count(r'\begin{definition}')==1
data=text.encode('utf-8'); E.write_bytes(data); P.write_bytes(data)
pattern=r'\\begin\{(theorem|lemma|proposition|corollary|conjecture|definition)\}.*?\\end\{\1\}'
before=[m.group() for m in re.finditer(pattern,old,re.S)]
after=[m.group() for m in re.finditer(pattern,text,re.S)]
out=dict(status='REVISED_SOURCE_PENDING_VERIFICATION',prior_sha256=hashlib.sha256(raw).hexdigest(),paper_sha256=hashlib.sha256(data).hexdigest(),prior_statements=len(before),current_statements=len(after),changed_prior_statements=[s for s in before if s not in text],added_statements=[s for s in after if s not in before],new_definitions=0,authors_and_hypersetup_preserved=True)
(H/'data/revision.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')
print(json.dumps({k:v for k,v in out.items() if not isinstance(v,list)},indent=2))
