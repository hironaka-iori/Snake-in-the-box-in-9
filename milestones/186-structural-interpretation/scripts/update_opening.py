from pathlib import Path
import re
H=Path('E:/Snake-in-a-box/milestones/186-structural-interpretation');D=Path('D:/Codex/2026-10-13/new-chat/outputs');R=H.parents[1]
for name in ['snake9_research.tex','snake9_frontier_explanation.tex']:
 src=D/name;old=src.read_bytes();backup=H/'source-before'/name
 assert not backup.exists();backup.write_bytes(old)
 if name!='snake9_research.tex':continue
 s=old.decode('utf-8');authors=re.findall(r'\\author\{[^\n]+',s);hyper=re.search(r'\\hypersetup\{.*?\n\}',s,re.S).group()
 abstract=r'''\begin{abstract}
Let $a(9)$ be the maximum edge length of an induced path in the
nine-dimensional binary hypercube. A verified construction gives
$a(9)\ge191$. The project retains an archived contributor proof of
$a(9)\le235$, whose complete independent rebuild remains pending.
For a snake of length $m$, singleton-square count $T$ and empty-square
count $s_0$, the exact identity
$T+2s_0+35(m+1)=9214$ converts local counting estimates into length bounds.

We prove local singleton-count restrictions, endpoint occurrence bounds
and integer-share identities that retain the contribution of empty
squares. Six and seven consecutive internal counts have sums at least
fourteen and sixteen. These improve the boundary contributions of the
two retained finite-graph arguments. The archived count-only estimate
then yields $39m+2s_0\le9192$, so a 235-edge snake would have at most
thirteen empty squares.

For the current share argument, the sufficient pending local floors are
$(15,14,14,14)$ on the direction patterns
$012034,012301,012340,012345$. With the stated count restrictions,
reference exclusions and graph-coverage premises, a retained-graph
potential gives $42254m+45L\le9928453$, where $L\ge0$ is the exact
division remainder in the share identity. It follows that $m\le234$.
A cycle and a 24-edge walk prove this comparison optimal for that fixed
profile and boundary accounting. The boundary argument, physical share
accounting and conditional numerical implication have passed Lean checks;
the finite potential has passed an exact integer scan.

All four required numerical share floors have native contradiction
certificates. Their complete Lean contradictions and geometric
interpretation remain unfinished, together with inherited local and
graph premises. The critical floor-fifteen certificate has been reduced
to 12,424 input clauses and 52,489 deductions. The current verification
work preserves this input while dividing its interpretation into smaller
proofs. Thus 234 remains conditional. No new unconditional numerical
upper bound is claimed, and the optimum and conjectured value 196 remain
unresolved.
\end{abstract}'''
 s=re.sub(r'\\begin\{abstract\}.*?\\end\{abstract\}',lambda _:abstract,s,count=1,flags=re.S)
 oldrow=r'Conditional bound 234 & The new boundary contribution 24 removes the positive-loss premise from the retained floor-17 comparison. Local shares, reference exclusions, count restrictions and the complete graph certificate remain separate obligations.\\'
 newrow=r'Conditional bound 234 & Profile $(15,14,14,14)$ and boundary contribution 24 give $42254m+45L\le9928453$. Complete local-share proofs, reference exclusions, count restrictions and the graph certificate remain pending.\\'
 assert oldrow in s;s=s.replace(oldrow,newrow)
 marker=r'\section{Remaining requirements for a stronger bound}\label{sec:closure}'
 addition=r'''
The current sufficient profile is $(15,14,14,14)$ on
$012034,012301,012340,012345$. Its proof requires completion of the local
certificates and their actual-snake interpretation, including the
extension condition used for $012301$ when $m\ge7$. It also retains the
specified six-count condition on $0123104$, reference and context
exclusions, graph coverage and the complete finite-edge certificate.
The older stronger profiles below record earlier proof obligations; they
are not additional numerical requirements of the current profile.

'''
 assert marker in s;s=s.replace(marker,marker+'\n'+addition,1)
 assert re.findall(r'\\author\{[^\n]+',s)==authors
 assert re.search(r'\\hypersetup\{.*?\n\}',s,re.S).group()==hyper
 src.write_text(s,encoding='utf-8',newline='\n');(R/'paper'/name).write_bytes(src.read_bytes())
(H/'scripts/update_opening.py').write_bytes(Path(__file__).read_bytes())
print('Updated abstract, evidence table and current dependency paragraph; preserved authors and hypersetup.')
