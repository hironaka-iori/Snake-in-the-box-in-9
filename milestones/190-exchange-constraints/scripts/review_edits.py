from pathlib import Path
import json,hashlib,re
R=Path('E:/Snake-in-a-box');H=R/'milestones/190-exchange-constraints';O=Path('D:/Codex/2026-10-13/new-chat/outputs')
main=O/'snake9_research.tex';short=O/'snake9_frontier_explanation.tex';a=main.read_text(encoding='utf-8');b=short.read_text(encoding='utf-8');old_a=a;old_b=b;edits=[]
def replace(s,old,new,key):
    assert s.count(old)==1,(key,s.count(old));edits.append(key);return s.replace(old,new,1)
a=replace(a,'\\begin{theorem}[Main result]\\label{thm:main}\nThe maximum edge length of an induced path in $\\Q_9$ satisfies','\\begin{theorem}[Verified construction and archived upper bound]\\label{thm:main}\nThe explicit construction and the archived contributor upper-bound argument\ngive the project interval','qualify-main-heading')
a=replace(a,'\\boxed{191\\le a(9)\\le235.}\n\\]\n\\end{theorem}','\\boxed{191\\le a(9)\\le235.}\n\\]\nThe upper bound is the archived contributor result; its complete independent\nrebuild remains pending.\n\\end{theorem}','qualify-main-evidence')
a=replace(a,'The proof of the upper bound has three steps.','The archived upper-bound argument has three steps.','qualify-roadmap')
a=replace(a,'Section~\\ref{sec:upper-proof} gives this argument directly for 235.','Section~\\ref{sec:upper-proof} records this argument for 235.','qualify-proof-section')
a=replace(a,'The current boundary-twenty-four comparison uses floor fifteen for all four pending shapes, as stated in Section~\\ref{sec:boundary-retuning}; these weaker local floors still need proofs.','The current boundary-twenty-four comparison uses the pending floors $(15,14,14,14)$ for $012034,012301,012340,012345$, respectively, as stated in Section~\\ref{sec:floor14-loss}; their complete Lean proofs and geometric interpretation remain unfinished.','current-floor-profile')
a=replace(a,'The global conclusion remains $191\\le a(9)\\le235$. The lower bound follows','The maintained project interval is $191\\le a(9)\\le235$, with the archived\nupper-bound qualification stated below. The lower bound follows','verification-interval-scope')
a=replace(a,'The earlier accepted-key conditional 234 profile uses share floors','The earlier sufficient accepted-key conditional 234 profile uses share floors','historical-profile-label')
needle='~\\cite{referenceunionarchive,potentialcertificatearchive,share152archive}.\n\nThe completed actual-snake results'
a=replace(a,needle,'~\\cite{referenceunionarchive,potentialcertificatearchive,share152archive}.\nThe current sufficient pending profile is $(15,14,14,14)$, as described in\nSection~\\ref{sec:floor14-loss}. The separate conditional-233 comparison\nand its four-unit share allowance retain their stated local-certificate\nand actual-snake integration requirements.\n\nThe completed actual-snake results','current-profile-pointer')
a=replace(a,'shapes remain unresolved~\\cite{share150archive,pilot151archive,share152archive}.','shapes remain unresolved at their original target floors\n~\\cite{share150archive,pilot151archive,share152archive}.','original-target-floor-scope')
a=replace(a,'Floor $18$ remains the requirement for $012034$ in the retained\nconditional profile.','For this earlier profile, floor $18$ is the requirement for $012034$.','historical-floor18')
a=replace(a,'research targets beyond the current conditional-234 argument.','research targets beyond the retained conditional comparisons.','historical-target-comparisons')
a=replace(a,'The target 196 and the maximum in dimension nine remain unresolved.\n\n\n\\subsection{Replacement restrictions','The target 196 and the maximum in dimension nine remain unresolved.\nThe exact data, computations and proof receipts for this comparison are\narchived in~\\cite{construction188archive}.\n\n\\subsection{Replacement restrictions','construction-evidence-citation')
a=replace(a,'The remaining construction problem therefore permits simultaneous\nchanges in separated parts of the 95-edge path, or changes to its\nsurrounding components and crossing vertices.','Further searches can allow a larger contiguous replacement, changes\nin separated parts of the 95-edge path, or changes to its surrounding\ncomponents and crossing vertices.','larger-contiguous-remains-open-main')
a=replace(a,'bound the maximum snake length in $Q_9$.\n\n\n\\section{Construction experiments','bound the maximum snake length in $Q_9$. The exact enumeration ranges,\nsolver inputs, outputs and verification receipts are archived\nin~\\cite{replacement189archive}.\n\n\\section{Construction experiments','replacement-evidence-citation')
b=replace(b,'\\textbf{1. The exact square budget.}\nWrite $v=m+1$','\\textbf{1. The exact square budget.}\nAssume $m\\ge1$; the single-vertex path satisfies the length bounds directly.\nWrite $v=m+1$','nontrivial-square-budget')
b=replace(b,'Let $W$ be the sum over all $m-8$ windows.','Assume $m\\ge8$; shorter paths already satisfy the stated upper bounds.\nLet $W$ be the sum over all $m-8$ windows.','window-domain')
b=replace(b,'If every traced edge satisfies\n$w(u,v)+p(u)-p(v)\\ge\\mu$ and the potential range is at most $R$,','For a nonnegative mean $\\mu$, suppose every traced edge satisfies\n$w(u,v)+p(u)-p(v)\\ge\\mu$ and the potential range is at most $R\\ge0$,','potential-sign-domain')
b=replace(b,'An exhaustive search excludes improvement by replacing any single\ninterval containing at most 42 internal vertices of the common','An exhaustive search excludes a two-edge improvement obtained by replacing\nany single interval containing at most 42 internal vertices of the common','two-edge-gain-scope')
b=replace(b,'The next constructive route must allow coordinated changes in\nseparated parts of the path or vary the surrounding components and\ncrossing vertices.','Further searches can allow a larger contiguous replacement, changes\nin separated parts of the path, or changes to the surrounding components\nand crossing vertices.','larger-contiguous-remains-open-short')
bibs=r'''
\bibitem{construction188archive}
I.~Hironaka, T.~Ma, and S.~Zhan. \emph{Constructions between dimensions six through nine}. Research record 188, 11 November 2026. Source sequences, coordinate cuts, finite comparisons and proof receipts:
\url{https://github.com/hironaka-iori/Snake-in-the-box-in-9/tree/11db4c849b1700ecc6dc5a67afcd5a8674738815/milestones/188-dimensional-constructions}.

\bibitem{replacement189archive}
I.~Hironaka, T.~Ma, and S.~Zhan. \emph{Restrictions on fixed-endpoint middle-path replacements}. Research record 189, 11 November 2026. Complete and partial enumeration ranges, exact solver models, outcomes and proof receipts:
\url{https://github.com/hironaka-iori/Snake-in-the-box-in-9/tree/2b7f244e6b5e7267e663d8e2aa88594c601975fe/milestones/189-middle-replacements}.
'''
a=replace(a,'\\end{thebibliography}',bibs+'\n\\end{thebibliography}','archive-bibliography')
for pattern in [r'\\author\{[^\n]+',r'\\hypersetup\{.*?\n\}']:assert re.search(pattern,a,re.S).group()==re.search(pattern,old_a,re.S).group()
main.write_text(a,encoding='utf-8',newline='\n');short.write_text(b,encoding='utf-8',newline='\n')
for n in [main.name,short.name]:(R/'paper'/n).write_bytes((O/n).read_bytes())
receipt={'coverage':{'main_source':'All original7820lines, split at4000 between two read-only reviewers. Root inspected and applied each actionable finding.','short_source':'All original630lines.'},'scope':'Manuscript-wide consistency, domain, evidence-status and editorial review; not an independent rebuild or verification of every mathematical proof.','reviewed_main_sha256':hashlib.sha256(old_a.encode()).hexdigest(),'reviewed_short_sha256':hashlib.sha256(old_b.encode()).hexdigest(),'base_commit':'2b7f244e6b5e7267e663d8e2aa88594c601975fe','edits':edits,'next_scheduled_review':200}
(H/'data/manuscript-review.json').write_text(json.dumps(receipt,indent=2)+'\n');(H/'scripts/review_edits.py').write_bytes(Path(__file__).read_bytes());print('APPLIED_REVIEW_EDITS',len(edits))
