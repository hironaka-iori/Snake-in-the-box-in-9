"""Add the fixed-profile credit obstruction to the existing paper in place."""
from pathlib import Path
import hashlib,json
H=Path(__file__).resolve().parents[1];R=H.parents[1]
paper=R/'paper/snake9_research.tex'
editor=Path('D:/Codex/2026-10-13/new-chat/outputs/snake9_research.tex')
sha=lambda b:hashlib.sha256(b).hexdigest()
raw=editor.read_bytes();assert raw==paper.read_bytes()
assert sha(raw)=='ca60f54607a0de2fc1b090016673215dfe32a7afedd360899cc43cda05e5d85a'
old=raw.decode('utf-8');anchor=r'\section{Remaining requirements for a stronger bound}\label{sec:closure}'
assert old.count(anchor)==1
addition=r'''\subsection{Uniform credit cannot replace the original share target}
\label{sec:share-credit-tradeoff}
Return to the original graph of 4947008 saved transitions used in
Section~\ref{sec:least-floors}. Fix the nine share floors, in the order
$012031,012032,012034,012301,012304,012310,012314,012340,012345$, at
\[
(16,15,18,16,16,12,16,16,16).
\]
Thus only the $012032$ floor is one below the sufficient floor profile.
Add a uniform credit $C\ge0$ on suffix $012032$ transitions whose second
and fourth internal count symbols are both below six and sum to at most
nine. Retain the occurrence allowance 24 and all other edge weights.

\begin{proposition}\label{prop:share15-credit-obstruction}
For this fixed graph and weight profile, every nonnegative potential mean
$\mu$ and potential range $R$ satisfy
\[
\frac{1098960+8\mu+24C+R}{4200+\mu}\ge235.
\]
Consequently, uniform occurrence credit cannot compensate for lowering
the $012032$ floor from 16 to 15 in this comparison.
\end{proposition}
\begin{proof}
A three-edge cycle has weights $616,496,376$ and no credited occurrence.
A second cycle has eleven edges, total weight $5452+4C$, and four credited
occurrences. A 28-edge walk has total weight 13280 and no credited occurrence.
Their edge identities, weights, event indicators and consecutive endpoints
were independently checked against the same saved graph~\cite{credittradeoffarchive}.
Summing a potential inequality around either cycle and along the walk gives
\[
\mu\le496,\qquad 11\mu\le5452+4C,\qquad 28\mu\le13280+R.
\]
The latter two inequalities imply $24C\ge66\mu-32712$ and
$R\ge28\mu-13280$. Therefore
\[
\begin{aligned}
\frac{1098960+8\mu+24C+R}{4200+\mu}
&\ge\frac{1052968+102\mu}{4200+\mu}\\
&=235+\frac{65968-133\mu}{4200+\mu}\ge235.
\end{aligned}
The denominator is positive and $65968=133\cdot496$. The arithmetic
implication has passed Lean under the three displayed graph inequalities.
\end{proof}

The three numerical constraints attain equality at
$\mu=496$, $C=1$ and $R=608$. This is equality in the displayed relaxation;
existence of a potential attaining these values on the full graph is not
asserted. The obstruction also applies to lower $012032$ floors by
monotonicity of the maximum-based edge weights. It leaves the share-16
profile and its conditional comparison below 235 intact. Later graphs with
additional exclusions or changed weights require their own checks.

'''
bib=r'''\bibitem{credittradeoffarchive}
I.~Hironaka, T.~Ma, and S.~Zhan, \emph{Uniform occurrence credit and the
original share-floor profile}, research archive, milestone 149.
\url{https://github.com/hironaka-iori/Snake-in-the-box-in-9/tree/main/milestones/149-share-credit-tradeoff}.

'''
assert old.count(r'\end{thebibliography}')==1
new=old.replace(anchor,addition+anchor).replace(r'\end{thebibliography}',bib+r'\end{thebibliography}')
assert old.split(r'\begin{document}',1)[0]==new.split(r'\begin{document}',1)[0]
assert new.count(r'\begin{definition}')==old.count(r'\begin{definition}')
assert '.lean' not in new
audit=H/'audit';audit.mkdir(exist_ok=True)
backup=audit/'paper-before149.tex.txt';assert not backup.exists();backup.write_bytes(raw)
out=new.encode('utf-8');editor.write_bytes(out);paper.write_bytes(out)
record=dict(status='PASS_TARGETED_CREDIT_OBSTRUCTION_PAPER_REVISION',
    source_sha256_before=sha(raw),source_sha256_after=sha(out),
    insertion_anchor=anchor,added_text=addition,added_bibliography_entry=bib,
    authors_and_preamble_unchanged=True,new_definitions=0,last_full_revision=146,next_full_revision=156)
(H/'data/paper-revision.json').write_text(json.dumps(record,indent=2)+'\n',encoding='utf-8')
print(json.dumps({k:v for k,v in record.items() if k not in ['added_text','added_bibliography_entry']}))
