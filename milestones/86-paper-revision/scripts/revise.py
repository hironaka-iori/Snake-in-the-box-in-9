"""Revise the existing editor source, retaining exact metadata and historical results."""
from pathlib import Path
import hashlib,json

HERE=Path(__file__).resolve().parents[1];ROOT=HERE.parents[1]
PAPER=ROOT/'paper/snake9_research.tex'
EDITOR=Path('D:/Codex/2026-10-13/new-chat/outputs/snake9_research.tex')
EXPECTED='3c67d4c168ee7fe463f2ea49da3459f2178ee2a655fd45f9ed374f88126f43dd'
sha=lambda b:hashlib.sha256(b).hexdigest()
for folder in ['data','logs','audit','text','scripts']:(HERE/folder).mkdir(exist_ok=True)
raw=EDITOR.read_bytes();assert raw==PAPER.read_bytes()
snapshot=HERE/'data/paper-before.tex.snapshot'
if sha(raw)!=EXPECTED:
    previous=json.loads((HERE/'data/revision.json').read_text())
    assert sha(raw)==previous['paper_sha256'],'Unrecorded edit: preserve it and review before proceeding'
    raw=snapshot.read_bytes()
assert sha(raw)==EXPECTED
if snapshot.exists():assert snapshot.read_bytes()==raw
else:snapshot.write_bytes(raw)
old=raw.decode('utf-8').replace('\r\n','\n');s=old

def replace(a,b):
    global s
    assert s.count(a)==1,(s.count(a),a[:100])
    s=s.replace(a,b)

def section(a,b,file):
    global s
    start=s.index(a);end=s.index(b,start)
    s=s[:start]+(HERE/'text'/file).read_text(encoding='utf-8')+'\n'+s[end:]

start=s.index(r'\begin{abstract}')+len(r'\begin{abstract}');end=s.index(r'\end{abstract}',start)
s=s[:start]+'\n'+r'''Let $a(9)$ be the maximum edge length of an induced path in the nine-dimensional binary hypercube. An explicit construction and an archived contributor proof give $191\le a(9)\le235$. We present the square census and local-count argument yielding $39m+2s_0\le9200$, where $s_0$ counts empty coordinate squares. Integer shares retain this empty-square term in local estimates. Count-independent share bounds are proved for five of the nine six-transition shapes, with four meeting the stronger target catalogue. Five-centre overlap and a boundary contribution of at least 21 singleton counts give an explicit potential criterion for the upper bound 234. The completed-local-share graph has minimum mean 483; the full target graph has mean 496 and range 600, but five local share bounds and parts of its arbitrary-snake interpretation remain pending. We construct the direction, history and count sequence, prove its retention under the completed short and history filters, and connect the reference table under two explicit catalogue premises. A cycle with all counts below six shows that bonuses confined to saturated counts cannot improve the completed graph's minimum mean. A separate one-premise comparison also falls short of 234. These obstructions identify specific limits of the current charge argument. The exact optimum and the numerical conjecture 196 remain unresolved.'''+ '\n'+s[end:]
replace('proves the history invariant, and explains a short-walk obstruction to weakening the catalogue.',
        'constructs the actual state sequence, proves the stated filter implications, and explains the short-walk and unsaturated-cycle obstructions.')
replace(r'\section{The current complete charge model}',r'\section{The current finite comparison graph and its interpretation}')
replace(r'$a(9)\le235$ & Geometric window reduction, 1287 catalogue keys, a complete potential check, and the endpoint summation.\\',
        r'$a(9)\le235$ & Archived contributor proof using 1287 local keys and a potential; the full independent rebuild remains pending.\\')
replace(r'Conditional bound 234 & Mean 496, range 600 and boundary loss 21; six local shares and the complete graph proof remain pending.\\',
        r'Conditional bound 234 & Mean 496, range 600 and boundary contribution 21; five local shares and the remaining graph proof are pending.\\')
replace(r'History and obstruction results & Checked suffix recognition and short-walk algebra; finite graph witnesses are independently computed.\\',
        r'Graph interfaces and obstructions & Checked state sequence and filter implications; exact finite cycles constrain further bonuses.\\')
replace('For six distinct directions, with shape $012345$, one has $H\\ge12$.',
        'For shape $012310$ and for six distinct directions, with shape $012345$, one has $H\\ge12$.')
replace('For the last shape, adjoining $H\\le11$ gives an inconsistent formula. The clause interpretations, contradiction certificates, coordinate transport and reversal have all passed Lean checks. Since $H$ is an integer, the exclusions give the stated bounds~\\cite{countfreearchive}.',
        'For each of the two remaining shapes, adjoining $H\\le11$ gives an inconsistent formula. The clause interpretations, contradiction certificates, coordinate transport and reversal have all passed Lean checks. Since $H$ is an integer, the exclusions give the stated bounds~\\cite{countfreearchive,shareclosurearchive}.')
replace(r'$012310$ & 12 & Pending\\',r'$012310$ & 12 & Checked\\')
replace('All nine target formulas have independently checked native Boolean refutations. Six still lack a completed Lean chain through the contradiction and geometric interpretation. Partial replay of the $012310$ case supplies no completed local theorem. The conditional catalogue dispatcher retains precisely these six premises. The classification and dispatcher are checked separately from those premises.',
        'All nine target formulas have independently checked native Boolean refutations. Five still lack a completed Lean chain through the contradiction and geometric interpretation. The $012310$ target now has a completed contradiction replay, arbitrary-coordinate interpretation and reversal. The conditional catalogue therefore retains precisely the five pending targets shown above. The classification and conditional combination are checked separately from those premises. For $012034$, clause interpretation has passed and contradiction replay is in progress; its target remains unproved~\\cite{shareclosurearchive,targetsharearchive}.')
replace('The reference exclusions contain 1378 distinct keys from the completed contributor count catalogues. Further recorded proofs supply forty recovered short-count restrictions, ten completed interval-count exclusions, the geometric share rules, and count-conditioned shares including Theorem~\\ref{thm:share120}. No unresolved additional count exclusion is required by this reference model. The complete interpretation of their table lookups for an arbitrary snake remains a separate obligation~\\cite{currentarchive}.',
        'The reference exclusions contain 1378 distinct keys from the contributor count catalogues. Further recorded proofs supply forty short-count restrictions, ten interval-count exclusions, three history exclusions, the geometric share rules and count-conditioned shares including Theorem~\\ref{thm:share120}. The count-filter implications are now connected to actual windows; the reference family retains two explicit closed catalogue premises in the current checking environment. Exact retained-transition membership and the interpretation of every credited share remain separate obligations~\\cite{currentarchive,interfacearchive}.')
replace('These guard implications and the five-count shift identities have passed Lean checks. They do not by themselves certify all exclusion lookups.',
        'These guard implications and the five-count shift identities are used in the checked filter arguments below. They preserve the distinction between exact counts and the interval represented by six.')
replace('The converse just given is a written consequence of maximality and prefix membership; no separate Lean check of that converse is claimed.',
        'The converse follows from maximality and prefix membership. The resulting exact equivalence and its numeric-history interpretation have also passed Lean checks~\\cite{interfacearchive}.')
marker=r'\subsection{Completed local bounds and conditional comparisons}'
replace(marker,(HERE/'text/state-and-filter-interface.tex').read_text(encoding='utf-8')+'\n'+marker)
section(marker,r'\subsection{A short-walk obstruction to weakening the catalogue}', 'comparisons.tex')
replace(r'\section{Remaining requirements for a stronger bound}\label{sec:closure}',
        (HERE/'text/bonus-criterion.tex').read_text(encoding='utf-8')+'\n'+
        (HERE/'text/unsaturated-obstruction.tex').read_text(encoding='utf-8')+'\n'+r'\section{Remaining requirements for a stronger bound}\label{sec:closure}')
section(r'\section{Remaining requirements for a stronger bound}\label{sec:closure}',r'\subsection{Sufficient charge inequalities}', 'closure.tex')
section(r'\section{Verification scope and remaining problem}\label{sec:verification}',r'\appendix','verification.tex')
refs=r'''\bibitem{shareclosurearchive}
I.~Hironaka, T.~Ma, and S.~Zhan. \emph{The count-independent share bound for 012310 and its completed-model comparison}. Research milestone 80, pinned revision \texttt{fadcb4bb}, 2 November 2026.
\url{https://github.com/hironaka-iori/Snake-in-the-box-in-9/tree/fadcb4bb1853601181c6456f2d5b89d93ef5eb05/milestones/80-012310-share-closure}.

\bibitem{interfacearchive}
I.~Hironaka, T.~Ma, and S.~Zhan. \emph{Direction coverage, actual state transitions, count-filter retention and the reference catalogue union}. Research milestones 77--79, 81, 84--85, included in pinned revision \texttt{22fbdbaa}, 2 November 2026.
\url{https://github.com/hironaka-iori/Snake-in-the-box-in-9/tree/22fbdbaac0ee80c4f8b0e9447466898bcb9a5841/milestones}.

\bibitem{unsaturatedarchive}
I.~Hironaka, T.~Ma, and S.~Zhan. \emph{A minimum-mean cycle with counts below six and its obstruction to additional charge}. Research milestone 82, pinned revision \texttt{444e7190}, 2 November 2026.
\url{https://github.com/hironaka-iori/Snake-in-the-box-in-9/tree/444e7190bc6c542465940c38b6cc763baa4bc85d/milestones/82-unsaturated-cycle-obstruction}.

\bibitem{targetsharearchive}
I.~Hironaka, T.~Ma, and S.~Zhan. \emph{The pending 012034 share certificate and exact single-target comparison}. Research milestone 83, pinned revision \texttt{344fe7e6}, 2 November 2026.
\url{https://github.com/hironaka-iori/Snake-in-the-box-in-9/tree/344fe7e659698280c6d85f66eb7d99da4abf00c1/milestones/83-012034-share-certificate}.

'''
replace(r'\bibitem{conditional234archive}',refs+r'\bibitem{conditional234archive}')
assert s.split(r'\begin{abstract}')[0]==old.split(r'\begin{abstract}')[0]
new=s.replace('\n','\r\n').encode('utf-8')
EDITOR.write_bytes(new);PAPER.write_bytes(new)
record=dict(status='REVISED_SOURCE_AWAITING_CHECKS',baseline_sha256=EXPECTED,paper_sha256=sha(new),
    paper_revision=86,previous_revision=76,next_scheduled_revision=96,
    editor=str(EDITOR),mirror=str(PAPER),metadata_preserved=True,
    changed_prior_statement_labels=['thm:countfree-completed'],
    additions={p.name:sha(p.read_bytes()) for p in sorted((HERE/'text').glob('*.tex'))},
    scope='Existing document edited in place. Compilation, independent review and mathematical/source checks are separate gates.')
(HERE/'data/revision.json').write_text(json.dumps(record,indent=2)+'\n')
print('REVISED_SOURCE',record['paper_sha256'])
