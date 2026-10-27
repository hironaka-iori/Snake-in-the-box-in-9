from pathlib import Path
import hashlib,json
HERE=Path(__file__).resolve().parents[1];ROOT=HERE.parents[1]
paper=ROOT/'paper/snake9_research.tex'
s=paper.read_text(encoding='utf-8')
s=s.replace(r'\section{The upper bound 236}',r'\section{The upper bound 235 and the retained empty-square term}')
s=s.replace('the nine normalized induced words, ten pairs','the nine induced words up to coordinate relabelling and reversal, ten pairs')
marker=r'\subsection{Five-window accounting and the current obstruction}'
assert s.count(marker)==1
addition=r'''\subsection{Joint charge and a conditional block estimate}
The count excess and empty-square share can be budgeted together. Put $z_j=24\delta_j+\sigma_{12}(x_j)$, and let $R_i$ be any valid lower bound for $\sum_{j=i+1}^{i+7}z_j$. Distinct seven-centre windows count each position at most seven times. Therefore
\[
\sum_i R_i\le7\left(24\sum_j\delta_j+\Sigma\right).
\]
If several bounds concern the same window charge, their maximum is valid. A count-excess bound $D_i\le\sum\delta_j$ and a share bound $L_i\le\sum\sigma_{12}(x_j)$ on that window give $24D_i+L_i\le\sum z_j$.

\begin{proposition}[Mixed common budget]\label{prop:mixed-common-budget}
Let $B=\sum_jb_j$, $D=\sum_j\delta_j$, and $G=24(B+D)+\Sigma$. Suppose nonnegative demands $Q,C,R$ satisfy
\[
Q\le7D,\qquad6C\le\Sigma,\qquad R\le7(24D+\Sigma).
\]
Then
\[
168B+R\le7G,\qquad
336B+24Q+42C+R\le14G.
\]
\end{proposition}
\begin{proof}
The first bound follows by substitution. For the second, use $24Q\le168D$, $42C\le7\Sigma$, and the assumed bound on $R$. The right side becomes $336B+336D+14\Sigma=14G$. The seven-window multiplicity and both algebraic implications have passed Lean. This argument uses separate copies of the same global budget, which explains the factor fourteen.
\end{proof}

The recorded sixteen-step count obstruction of mean $65/16$ illustrates the effect of disjoint shares. Two applicable share-96 windows occupy the cyclic position sets $\{13,14,15,0,1\}$ and $\{6,7,8,9,10\}$. These sets are disjoint. Under their local share premises, a complete period receives at least 192 share units, and its normalized charge is at least
\[
\frac{24\cdot65+192}{24\cdot16}=\frac{73}{16}.
\]
For $p\ge1$ consecutive periods on a line, one crossing window is lost at the boundary. The corresponding conditional share estimate is $\Sigma\ge96(2p-1)$, with the remaining unused boundary shares nonnegative. The finite disjoint-group summation has been checked in Lean.

\begin{proposition}[Conditional finite-block consequence]\label{prop:finite-block-conditional}
Suppose $p\ge1$, $T\ge v+49p+6$, $\Sigma\ge96(2p-1)$, and $24T+\Sigma+840v\le221136$. Then
\[
864v+1368p\le221088.
\]
In particular, these premises are inconsistent with $v=236$ and $p\ge13$.
\end{proposition}
\begin{proof}
Substituting the two lower bounds in the charge inequality gives
$864v+1368p+48\le221136$. At $v=236$ and $p=13$, its left side without the constant is $221688>221088$. Larger $p$ only increases it. These implications have passed Lean. A full deduction of the stated count and share premises from an arbitrary snake run remains unfinished, so this proposition is not an unconditional exclusion of such runs.
\end{proof}

'''
s=s.replace(marker,addition+marker)
s=s.replace('Lean checks the displayed sum, general telescoping implication, and zero-credit packing identity.','Lean checks the displayed sum, general telescoping implication, and zero-credit packing identity~\\cite{packingarchive}.')
s=s.replace(r'\end{thebibliography}',r'''\bibitem{packingarchive}
I.~Hironaka, T.~Ma, and S.~Zhan. \emph{Zero-credit packing limitation and manuscript revision}. Research milestone 56.
\url{https://github.com/hironaka-iori/Snake-in-the-box-in-9/tree/main/milestones/56-packing-limit-and-revision}.

\end{thebibliography}''')
paper.write_text(s,encoding='utf-8',newline='\n')
Path('D:/Codex/2026-10-13/new-chat/outputs/snake9_research.tex').write_bytes(paper.read_bytes())
receipt=json.loads((HERE/'data/paper-revision.json').read_text())
receipt['after_sha256']=hashlib.sha256(paper.read_bytes()).hexdigest()
(HERE/'data/paper-revision.json').write_text(json.dumps(receipt,indent=2)+'\n')
