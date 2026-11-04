"""Full revision156 after complete-source reviews; preserve prior proof content."""
from pathlib import Path
from collections import Counter
import hashlib,json,re

H=Path(__file__).resolve().parents[1];R=H.parents[1]
P=R/'paper/snake9_research.tex'
EDITOR=Path('D:/Codex/2026-10-13/new-chat/outputs/snake9_research.tex')
EXPECTED='b3b06d3df379436f81b59d723d80bd01902d566e6d0617ceb860b155e4186e80'
read=lambda p:json.loads(Path(p).read_text(encoding='utf-8-sig'))
sha=lambda b:hashlib.sha256(b).hexdigest()

ABSTRACT=r'''Let $a(9)$ be the maximum edge length of an induced path in the
nine-dimensional binary hypercube. An explicit construction and an archived
contributor proof give $191\le a(9)\le235$; a complete independent rebuild
of the upper-bound proof remains pending. The exact square census
$T+2s_0+35(m+1)=9214$ retains both the singleton-square count $T$ and the
empty-square count $s_0$ for a snake of length $m$.
We develop local count restrictions, endpoint occurrence bounds and integer
shares of empty squares. Completed results include the sharp pair bound
eight on $012032$, a bound of twenty-four low-pair windows, a five-count
sum of at least nineteen on $012310$, the universal $012032$ share floor
16, and a stronger floor 17 under specified local count conditions.
The conditional comparison giving 234 still requires four local share
theorems, reference refutations and the complete potential certificate.
For a further retained finite graph with its additional count assumptions,
an exact computation and cycle-and-walk inequalities determine the best
comparison after the stronger share is installed: $235-15/2348$, attained
at mean 496, range 602 and zero uniform occurrence credit. Thus retuning
those parameters cannot strengthen this fixed comparison. This finite-graph
conclusion does not establish a new snake bound. The optimum and the
numerical conjecture 196 remain open.
'''

NEW_RESULT=r'''\subsection{Exact optimum of the strengthened comparison}\label{sec:range156}
The preceding obstructions use specified earlier weight profiles. We now
install all nine conditional floors, in the order of the catalogue in
Section~\ref{sec:countfree-catalogue}:
\[
(16,16,18,16,16,12,16,16,16).
\]
The count-conditioned floor 17 from
Theorem~\ref{thm:critical-count-share17} enters the maximum for the
six-transition suffix only. Prefix and suffix representations of the same
occurrence are not added. The three existing count bonuses still enter
through their common maximum. The graph retains 4661572 of the original
4947008 transitions and all 1601856 states.

The graph's additional count restrictions, the proposed six-count floor
25 on $0123104$, and its odd-length pair restriction remain assumptions
of an application to snakes. The four unresolved share floors and the
reference and potential-assembly obligations also remain. The calculation
below is a statement about this specified finite graph.

\begin{proposition}[Optimal retained-graph comparison]\label{prop:range156-optimum}
For this graph and weight profile, allow a nonnegative rational credit $C$
on each recorded low-pair occurrence edge, with boundary cost $24C$.
Every valid rational potential with nonnegative mean $\mu$ and range $R$
satisfies
\[
\frac{1098960+8\mu+24C+R}{4200+\mu}
\ge\frac{551765}{2348}
=235-\frac{15}{2348}>234.
\]
The lower bound is attained by the recorded potential with
$\mu=496$, $C=0$, and $R=602$. Equality forces these three parameter values.
\end{proposition}
\begin{proof}
The retained fourteen-cycle has total weight 6944 and no occurrence event,
so summing its potential inequalities gives $\mu\le496$ for every $C\ge0$.
A retained nine-edge walk has successive weights
\[
(252,378,496,496,616,496,496,376,256).
\]
Their sum is 3862. None of these edges has an occurrence event or receives
the new share-17 increment. Telescoping along this walk gives
\[
9\mu\le3862+R.
\]
Consequently, for $\mu,C\ge0$,
\[
\frac{1098960+8\mu+24C+R}{4200+\mu}
\ge\frac{1095098+17\mu+24C}{4200+\mu}
\ge\frac{551765}{2348}.
\]
The middle expression increases with $C$ and decreases with
$\mu$ on $0\le\mu\le496$. Equality requires $C=0$, $\mu=496$ and then
$R=602$. The cycle inequality, walk inequality, rational comparison and
equality conditions have passed Lean checks.

The recorded range-602 potential was checked by exact integer arithmetic
on all 4661572 newly weighted edges. Its minimum slack is zero. A separate
audit recovered the nine walk rows and fourteen cycle rows from the
original column data, verified their retention, weights and overlaps,
and found zero occurrence events on both witnesses. This numerical
certificate supplies attainment for the finite graph. It does not
complete the separate Lean edge certificate or its interpretation for
arbitrary snakes~\cite{range156archive}.
\end{proof}

The hypothesis that the new share estimate would reduce the range below
602 is therefore refuted for this profile. Although 77 retained edge
weights increase, none belongs to either obstruction. Increasing weights
or deleting edges elsewhere preserves both lower-bound witnesses and
the feasible recorded potential, so it cannot change this optimum.
A further improvement must alter at least one witness or the comparison
itself. The conditional integer conclusion remains 234; its unresolved
geometric and certificate premises are not discharged by this optimization.

'''

BIB=r'''\bibitem{range156archive}
I.~Hironaka, T.~Ma, and S.~Zhan. \emph{Exact retained-graph range and
joint comparison obstruction}. Research record 156, 4 November 2026.
\url{https://github.com/hironaka-iori/Snake-in-the-box-in-9/tree/main/milestones/156-potential-range-and-paper}.

'''

def transform(text):
    operations=[]
    def replace(old,new):
        nonlocal text
        assert text.count(old)==1,(old[:100],text.count(old))
        text=text.replace(old,new);operations.append(dict(kind='replace',before=old,after=new))
    def move(block,marker,intro=''):
        nonlocal text
        assert text.count(block)==1 and text.count(marker)==1
        text=text.replace(block,'');text=text.replace(marker,intro+block+'\n'+marker)
        operations.append(dict(kind='move',block_sha256=sha(block.encode()),destination=marker,introduction=intro))
    for row in read(H/'data/paper-replacements.json'):replace(row['before'],row['after'])
    start=text.index(r'\begin{abstract}')+len(r'\begin{abstract}')
    end=text.index(r'\end{abstract}',start)
    replace(text[start:end],'\n'+ABSTRACT+'\n')

    start=text.index(r'\begin{theorem}[Count-conditioned share on $012032$]')
    end=text.index(r'\end{proof}',start)+len(r'\end{proof}')
    block=text[start:end]
    move(block,'The original nine-shape target is displayed below.',
        '\\subsection{A stronger share under specified counts}\n')
    replace('The compact core is unchanged. Its interpretation and coordinate and\nreversal transfer have passed Lean in 98 modules. The complete 137-module\ncontradiction replay and the final application to actual snakes have also\npassed Lean, giving the following local theorem.',
        'The compact core is unchanged. Its 98 interpretation and coordinate/reversal\nmodules, 137 complete contradiction-replay modules and final actual-snake\napplication have passed Lean. These checks establish\nTheorem~\\ref{thm:critical-count-share17}.')

    start=text.index(r'\subsection{Uniform credit cannot replace the original share target}')
    end=text.index(r'\section{Remaining requirements for a stronger bound}',start)
    block=text[start:end]
    move(block,r'\subsection{When an added charge can improve the cycle mean}')

    start=text.index('Broadening the count conditions does not add credit to the retained graph')
    end=text.index('For the preserved $012034$ share-18 proof,',start)
    block=text[start:end]
    move(block,r'\section{Remaining requirements for a stronger bound}')
    replace(r'\section{Remaining requirements for a stronger bound}',NEW_RESULT+r'\section{Remaining requirements for a stronger bound}')
    replace('These three\nlocal targets therefore require a joint analysis, followed by the remaining\ngraph and proof obligations.',
        'The joint finite comparison after installing these floors and the\ncount-conditioned share 17 is determined by\nProposition~\\ref{prop:range156-optimum}. The remaining local premises,\ngraph interpretation and proof obligations are separate.')
    replace('These local\nchanges require their own complete edge and range checks.',
        'These local changes are included in the finite check in\nProposition~\\ref{prop:range156-optimum}.') if 'These local\nchanges require their own complete edge and range checks.' in text else None

    start=text.index('The saved-cycle obstructions concern their stated graph, weights and')
    end=text.index(r'\appendix',start)
    replace(text[start:end],r'''The saved-cycle obstructions retain their specified graphs and weights.
Proposition~\ref{prop:range156-optimum} gives the exact joint comparison
for the strengthened retained profile. The numerical edge scan and the
Lean-checked cycle, walk and rational deductions have different scopes:
neither discharges the additional geometric premises or the outstanding
reference and edge-certificate requirements. No construction above 191 or
matching optimality theorem has been obtained. The numerical conjecture
196 is used in none of the proved bounds. Section~\ref{sec:closure} states
the remaining requirements.

''')
    row='Low-pair occurrence bound & At most twenty-four $012032$ windows have pair sum at most nine, with at most twelve assigned to either endpoint.\\\\'
    replace(row,row+r'''
Local share bounds on $012032$ & Universal floor 16 and floor 17 under the count conditions of Theorem~\ref{thm:critical-count-share17}.\\
Strengthened retained comparison & Exact finite optimum $235-15/2348$; its geometric and certificate premises remain separate.\\''')
    replace(r'\end{thebibliography}',BIB+r'\end{thebibliography}')
    return text,operations

def invariants(old,new):
    assert old.split(r'\begin{document}',1)[0]==new.split(r'\begin{document}',1)[0]
    patterns={
        'statements':r'\\begin\{(theorem|proposition|lemma|corollary|conjecture|definition)\}.*?\\end\{\1\}',
        'proofs':r'\\begin\{proof\}.*?\\end\{proof\}',
        'display_math':r'\\\[.*?\\\]',
        'equation_math':r'\\begin\{(equation\*?|align\*?|alignat\*?|gather\*?|multline\*?)\}.*?\\end\{\1\}',
        'witness_quotes':r'\\begin\{quote\}.*?\\end\{quote\}',
        'long_tables':r'\\begin\{longtable\}.*?\\end\{longtable\}'}
    counts={}
    for name,pattern in patterns.items():
        a=Counter(m[0] for m in re.finditer(pattern,old,re.S));b=Counter(m[0] for m in re.finditer(pattern,new,re.S))
        assert not a-b,(name,list((a-b).keys())[:1])
        counts[name]=dict(before=sum(a.values()),after=sum(b.values()),all_original_bytes_preserved=True)
    assert old.count(r'\begin{definition}')==new.count(r'\begin{definition}')
    for pattern in [r'\\label\{([^}]+)\}',r'\\bibitem(?:\[[^]]*\])?\{([^}]+)\}']:
        a=re.findall(pattern,old);b=re.findall(pattern,new)
        assert len(b)==len(set(b)) and set(a)<=set(b)
    assert '.lean' not in new and 'Snake9.' not in new
    return counts

def main():
    raw=P.read_bytes();assert raw==EDITOR.read_bytes() and sha(raw)==EXPECTED
    local=read(R/'milestones/155-share17-replay/data/actual-snake-completion.json')
    result=read(H/'data/share17-range496/result.json')
    audit=read(H/'review/walk-audit.json');lean=read(H/'data/range-lean-check.json')
    assert local['status']=='PASS_ACTUAL_SNAKE_SHARE17_WITH_COUNT_CONDITIONS'
    assert result['status']=='PASS_MINIMUM_RANGE_AT_MEAN496' and result['potential_range']==602
    assert audit['status']=='PASS_SELECTED_ROW_WALK_AND_CYCLE_AUDIT'
    assert audit['uniform_credit']['walk_occurrences']==audit['uniform_credit']['cycle_occurrences']==0
    assert lean['status']=='PASS' and len(lean['axioms'])==7
    for p,d in lean['dependencies'].items():assert sha(Path(p).read_bytes())==d,p
    for path in [H/'review/main-body-review.md',H/'review/appendix-review.md']:
        assert EXPECTED in path.read_text(encoding='utf-8')
    old=raw.decode('utf-8');new,operations=transform(old);preserved=invariants(old,new)
    backup=H/'audit/paper-before156.tex.txt';receipt=H/'data/paper-revision.json'
    assert not backup.exists() and not receipt.exists()
    backup.parent.mkdir(exist_ok=True);backup.write_bytes(raw)
    output=new.encode('utf-8')
    assert P.read_bytes()==EDITOR.read_bytes()==raw
    try:
        P.write_bytes(output);EDITOR.write_bytes(output)
        assert P.read_bytes()==EDITOR.read_bytes()==output
    except BaseException:
        P.write_bytes(raw);EDITOR.write_bytes(raw);raise
    inputs=[Path(__file__),H/'data/paper-replacements.json',H/'review/main-body-review.md',
        H/'review/appendix-review.md',H/'review/walk-audit.json',H/'data/range-lean-check.json',
        H/'data/share17-range496/result.json']
    record=dict(status='FULL_SOURCE_REVISION156_SAVED_COMPILATION_PENDING',
        source_sha256_before=EXPECTED,source_sha256_after=sha(output),operations=operations,
        preserved=preserved,authors_preamble_hypersetup_unchanged=True,new_definitions=0,
        full_source_review=True,new_global_bound=False,full_revision=156,next_full_revision=166,
        source_files_sha256={p.relative_to(R).as_posix():sha(p.read_bytes()) for p in inputs})
    receipt.write_text(json.dumps(record,indent=2)+'\n',encoding='utf-8',newline='\n')
    print(json.dumps({k:record[k] for k in ['status','source_sha256_after','preserved','new_definitions']}))

if __name__=='__main__':main()
