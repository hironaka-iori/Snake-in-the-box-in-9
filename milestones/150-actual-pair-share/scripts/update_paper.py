"""Record the checked conditional012032 transfer in both existing paper copies."""
from pathlib import Path
import hashlib,json
H=Path(__file__).resolve().parents[1];R=H.parents[1]
sha=lambda b:hashlib.sha256(b).hexdigest()
read=lambda p:json.loads(p.read_text(encoding='utf-8-sig'))
assert read(H/'data/semantics-completion.json')['status']=='PASS_CORE_SEMANTICS_AND_CONDITIONAL_ACTUAL_SNAKE_SHARE16'
paper=R/'paper/snake9_research.tex';editor=Path('D:/Codex/2026-10-13/new-chat/outputs/snake9_research.tex')
raw=editor.read_bytes();assert raw==paper.read_bytes()
assert sha(raw)=='d8d8db8d88c0f26a5d46fdbe4736df8df523e9d9740e455318405e7c275e72b0'
old=raw.decode('utf-8')
anchor='For the preserved $012034$ share-18 proof, the original-clause assignment'
assert old.count(anchor)==1
addition=r'''The $012032$ target now has a separate count-free certificate. A search
with the additional condition $\alpha_{r+2}+\alpha_{r+4}\ge10$ produced
a retained proof using none of that condition's added clauses or variables.
All 13655 core clauses belong to the original model with share sum at most
15. An independent replay checks all 58182 deductions and 5350080
propagation references, ending in the empty clause. The absence of the
additional pair condition was checked against the complete original input.

All core-clause interpretations and the actual-snake transfer have passed
Lean in 112 modules. Conditional on a contradiction of this exact core,
every fitting window whose forward or reversed canonical directions are
$012032$ satisfies
\[
\sum_{j=1}^{5}\sigma_{12}(x_{r+j})\ge16.
\]
No additional count, parity or endpoint-location hypothesis is required.
The complete numerical proof has also been transported to a packed replay
with 878 segments. Its initial-tree and prefix sources are prepared; they
have not yet been checked in Lean. The full contradiction therefore remains
an explicit premise, and this target is still among the uncompleted local
share theorems~\cite{share150archive}.

'''
bib=r'''\bibitem{share150archive}
I.~Hironaka, T.~Ma, and S.~Zhan, \emph{A count-free certificate and
conditional actual-snake share bound for 012032}, research archive,
milestone 150.
\url{https://github.com/hironaka-iori/Snake-in-the-box-in-9/tree/main/milestones/150-actual-pair-share}.

'''
new=old.replace(anchor,addition+anchor).replace(r'\end{thebibliography}',bib+r'\end{thebibliography}')
assert old.split(r'\begin{document}',1)[0]==new.split(r'\begin{document}',1)[0]
assert old.count(r'\begin{definition}')==new.count(r'\begin{definition}') and '.lean' not in new
backup=H/'audit/paper-before150.tex.txt';assert not backup.exists();backup.write_bytes(raw)
out=new.encode('utf-8');editor.write_bytes(out);paper.write_bytes(out)
record=dict(status='PASS_TARGETED_CONDITIONAL_SHARE_PAPER_REVISION',source_sha256_before=sha(raw),
    source_sha256_after=sha(out),insertion_anchor=anchor,added_text=addition,added_bibliography_entry=bib,
    authors_and_preamble_unchanged=True,new_definitions=0,last_full_revision=146,next_full_revision=156)
(H/'data/paper-revision.json').write_text(json.dumps(record,indent=2)+'\n',encoding='utf-8')
print(json.dumps({k:v for k,v in record.items() if k not in ['added_text','added_bibliography_entry']}))
