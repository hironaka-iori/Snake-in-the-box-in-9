"""Record checked broader semantics while retaining the unproved contradiction."""
from pathlib import Path
import hashlib,json
H=Path(__file__).resolve().parents[1];R=H.parents[1]
read=lambda p:json.loads(p.read_text(encoding='utf-8-sig'))
sha=lambda b:hashlib.sha256(b).hexdigest()
complete=read(H/'data/semantics-completion.json')
assert complete['status']=='PASS_BROADER_CORE_SEMANTICS_AND_CONDITIONAL_ACTUAL_SNAKE_SHARE17'
assert complete['core_unsat_is_explicit_premise'] and not complete['complete_contradiction_checked']
paper=R/'paper/snake9_research.tex';editor=Path('D:/Codex/2026-10-13/new-chat/outputs/snake9_research.tex')
raw=paper.read_bytes();assert raw==editor.read_bytes()
assert sha(raw)=='2dac2eda58da060c053f415c90bcd4d7075a1b236e9838a65f473945913d8513'
old=raw.decode('utf-8');new=old;changes=[]
def replace(before,after):
    global new
    assert new.count(before)==1,(before,new.count(before))
    new=new.replace(before,after);changes.append(dict(before=before,after=after))
replace(r'''The compact core is unchanged. These certificates support share at least
17 under the displayed hypotheses; their Lean clause interpretation,
complete contradiction replay and application to arbitrary snakes remain
unfinished. The generated exact-count sources do not yet interpret the
broader conditions. No completed local theorem is asserted here.''',r'''The compact core is unchanged. Its broader clause interpretation and
transfer to arbitrary coordinates and reversed windows have now passed
Lean in 98 modules. This establishes the share-17 implication under an
explicit unsatisfiability premise for that core. The complete contradiction
replay remains unfinished, so the share-17 bound under the displayed count
hypotheses is still conditional~\cite{broader154archive}.

Broadening the count conditions does not add credit to the retained graph
used for the saved critical cycles. That graph already requires
$\alpha_{r+2}+\alpha_{r+4}\ge9$ in this context. Together with
$\alpha_{r+2}\le4$ and $\alpha_{r+4}\le5$, this forces the two counts
to equal 4 and 5. An inventory finds 100 additional matching rows in the
source graph, all already excluded from the retained graph. This
calculation concerns that graph and its removal hypotheses.''')
bib=r'''\bibitem{broader154archive}
I.~Hironaka, T.~Ma, and S.~Zhan, \emph{Broader critical-window share
interpretation and its retained-graph effect}, research archive, milestone 154.
\url{https://github.com/hironaka-iori/Snake-in-the-box-in-9/tree/main/milestones/154-share17-broader-semantics}.

'''
replace(r'\end{thebibliography}',bib+r'\end{thebibliography}')
assert old.split(r'\begin{document}',1)[0]==new.split(r'\begin{document}',1)[0]
assert old.count(r'\begin{definition}')==new.count(r'\begin{definition}')
assert '.lean' not in new
backup=H/'audit/paper-before154.tex.txt';assert not backup.exists();backup.write_bytes(raw)
out=new.encode('utf-8');paper.write_bytes(out);editor.write_bytes(out)
record=dict(status='PASS_BROADER_SEMANTICS_PAPER_REVISION',source_sha256_before=sha(raw),
    source_sha256_after=sha(out),prose_replacements=changes,authors_and_preamble_unchanged=True,
    new_definitions=0,last_full_revision=146,next_full_revision=156)
(H/'data/paper-revision.json').write_text(json.dumps(record,indent=2)+'\n',encoding='utf-8')
print(json.dumps({k:v for k,v in record.items() if k!='prose_replacements'}))
