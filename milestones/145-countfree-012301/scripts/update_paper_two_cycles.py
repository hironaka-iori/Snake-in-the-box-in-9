"""Add the independently reproducible two-cycle obstruction to the same paper."""
from pathlib import Path
import hashlib,json
H=Path(__file__).resolve().parents[1];R=H.parents[1]
read=lambda p:json.loads(p.read_text(encoding='utf-8-sig'))
assert read(H/'data/TwoCycles145-audit.json')['status']=='PASS'
assert read(H/'data/two-cycle-analysis.json')['status']=='PASS_EXACT_TWO_SAVED_CYCLE_AUDIT'
p=Path('D:/Codex/2026-10-13/new-chat/outputs/snake9_research.tex');q=R/'paper/snake9_research.tex'
b=p.read_bytes();assert b==q.read_bytes() and hashlib.sha256(b).hexdigest()=='39064731522e4fbaae01f55d88e3a128ebf7c3e4e72bb425f208c48d0fb8e4c2'
s=b.decode('utf-8')
addition=r'''The preceding eleven-cycle strengthens this restriction. It uses only the
suffix shapes $012032$, $012314$ and $012031$, has base total $5399$,
and contains four occurrence events. Consequently neither $F$ nor $G$
changes its weights, and it always imposes
\[
11\mu\le5399+4C.
\]
With $B=24$, combining this inequality with the two-edge range inequality
and a comparison below $235$ gives $11329-11F<636C$. Eliminating $C$
using~\eqref{eq:joint-share-necessary} yields the stronger necessary condition
\begin{equation}\label{eq:two-cycle-share-necessary}
325F+159G>9074.
\end{equation}
In particular, retaining the eleven-cycle unchanged while fixing $F=16$
requires integer $G\ge25$. This supersedes the weaker requirement $G\ge12$
obtained from the fourteen-cycle alone.

\begin{proposition}\label{prop:two-cycle-share16-obstruction}
Keep these two cycles, their other weights, and the occurrence allowance
$B=24$ fixed. Share floors at most $16$ for each of $012301$ and $012340$,
together with any uniform occurrence credit and any $012034$ floor,
leave the comparison at least
\[
\frac{551875}{2348}=235+\frac{95}{2348}>235.
\]
\end{proposition}
\begin{proof}
It is enough to use the edge-weight upper bounds with $F=G=16$.
The fourteen-cycle gives $\mu\le496$ and $R\ge2\mu-512$.
The eleven-cycle gives $24C\ge66\mu-32394$. Therefore
\[
\frac{1098960+8\mu+24C+R}{4200+\mu}
\ge\frac{1066054+76\mu}{4200+\mu}
\ge\frac{551875}{2348}.
\]
The last ratio decreases with $\mu\ge0$, so the final inequality follows
from $\mu\le496$. Lean checks the implication and the exact gap above $235$.
The listed arithmetic constraints attain equality at
$\mu=496$, $C=57/4$ and $R=480$. This establishes the optimum of this
arithmetic relaxation only; no full-graph potential is asserted.
\end{proof}

The existing $012032$ share-$16$ target is therefore relevant in addition
to the two share floors above. It adds $57$ to the eleven-cycle total,
raising that cycle's mean to $496$ at zero occurrence credit. The three
proposed share floors then give mean $496$ on both saved cycles without
occurrence credit. The other graph cycles, local proofs and global
interpretation remain separate obligations.

'''
marker='The saved Boolean certificate for $012301$ at cap $15$ has now been'
assert s.count(marker)==1;s=s.replace(marker,addition+marker)
new=s.encode('utf-8');p.write_bytes(new);q.write_bytes(new)
record=read(H/'data/paper-revision.json');record['intermediate_sha256']=record['after_sha256']
record['after_sha256']=hashlib.sha256(new).hexdigest();record['additional_result']='Two-cycle obstruction and325F+159G>9074 necessary tradeoff'
(H/'data/paper-revision.json').write_text(json.dumps(record,indent=2)+'\n');print(record['after_sha256'])
