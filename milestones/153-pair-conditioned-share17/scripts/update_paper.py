"""Record the critical-context numerical certificate with explicit unchecked steps."""
from pathlib import Path
import hashlib,json
H=Path(__file__).resolve().parents[1];R=H.parents[1]
read=lambda p:json.loads(p.read_text(encoding='utf-8-sig'))
sha=lambda b:hashlib.sha256(b).hexdigest()
assert read(H/'broader/verification.json')['status']=='PASS_BROADER_CONDITIONS_NATIVE_RUP_REPLAY'
assert read(H/'replay/data/packed-replay.json')['status']=='PASS_COMPLETE_RENAMED_AND_PACKED_RUP_REPLAY'
paper=R/'paper/snake9_research.tex';editor=Path('D:/Codex/2026-10-13/new-chat/outputs/snake9_research.tex')
raw=paper.read_bytes();assert raw==editor.read_bytes()
assert sha(raw)=='4d4c7a43d188d05bef483f30e4c55892cceb45b1978f2a6e4d188927eb262bcd'
old=raw.decode('utf-8')
anchor='For the preserved $012034$ share-18 proof, the original-clause assignment'
paragraph=r'''A separate certificate targets the $012032$ windows on the surviving
eleven-cycle. A proposed improvement restricted to
$\alpha_{r+2}+\alpha_{r+4}\ge10$ leaves that cycle unchanged: all four
of its $012032$ windows have exact pair sum nine. The companion
fourteen-cycle contains no $012032$ window. This observation concerns
these cycles and does not rule out improving the potential elsewhere.

The five-count context $(4,4,4,5,3)$ instead occurs on the eleven-cycle.
Adjoining share at most 16 to its necessary local conditions gives a
certificate with 11869 retained clauses, 30305 deductions and 1754767
propagation references. Complete numerical replay reaches the empty clause.
The retained proof uses none of the registers enforcing the lower bounds
on the second and fourth counts. Removing those counters and relabelling
every retained clause and proof step gives a second complete numerical
replay under the broader conditions
\[
\alpha_{r+1}=4,\qquad \alpha_{r+2}\le4,\qquad
\alpha_{r+3}=4,\qquad \alpha_{r+4}\le5,\qquad
\alpha_{r+5}=3.
\]
The compact core is unchanged. These certificates support share at least
17 under the displayed hypotheses; their Lean clause interpretation,
complete contradiction replay and application to arbitrary snakes remain
unfinished. The generated exact-count sources do not yet interpret the
broader conditions. No completed local theorem is asserted here.

If the exact-context result and its reversal are established, they raise
two edges of the eleven-cycle by one relative to the profile imposing
universal $012032$ share 16. Its total then increases from 5456 to 5458.
The fourteen-cycle remains unchanged, and this calculation alone gives
no improved global bound~\cite{critical153archive}.

'''
assert old.count(anchor)==1
new=old.replace(anchor,paragraph+anchor)
bib=r'''\bibitem{critical153archive}
I.~Hironaka, T.~Ma, and S.~Zhan, \emph{Critical-window share certificates
and removal of two unused count assumptions}, research archive, milestone 153.
\url{https://github.com/hironaka-iori/Snake-in-the-box-in-9/tree/main/milestones/153-pair-conditioned-share17}.

'''
assert new.count(r'\end{thebibliography}')==1
new=new.replace(r'\end{thebibliography}',bib+r'\end{thebibliography}')
assert old.split(r'\begin{document}',1)[0]==new.split(r'\begin{document}',1)[0]
assert '.lean' not in new and old.count(r'\begin{definition}')==new.count(r'\begin{definition}')
backup=H/'audit/paper-before153.tex.txt';assert not backup.exists();backup.write_bytes(raw)
out=new.encode('utf-8');paper.write_bytes(out);editor.write_bytes(out)
record=dict(status='PASS_NUMERICAL_CERTIFICATE_PAPER_REVISION',source_sha256_before=sha(raw),source_sha256_after=sha(out),
    prose_replacements=[dict(before=anchor,after=paragraph+anchor)],added_bibliography_entry=bib,
    authors_and_preamble_unchanged=True,new_definitions=0,actual_snake_theorem_claimed=False,last_full_revision=146,next_full_revision=156)
(H/'data/paper-revision.json').write_text(json.dumps(record,indent=2)+'\n',encoding='utf-8')
# Keep the published152 script unchanged; prepare a successor for this paper version.
prior=R/'milestones/152-countfree-share16-completion/scripts/update_paper.py'
s=prior.read_text(encoding='utf-8').replace(sha(raw),sha(out))
needle="replace('Allow only the five unfinished floors to decrease to',"
assert s.count(needle)==1
addition=r'''replace(r'''+'"""'+r'''\item For 234, additionally prove the five local shares
$(16,18,16,16,16)$ for $012032,012034,012301,012340,012345$, including
their geometric interpretation and reversal. The completed profile needs
none of these additional share assumptions and currently recovers 235.'''+ '"""'+r''',
        r'''+'"""'+r'''\item For 234, complete the remaining local shares
$(18,16,16,16)$ for $012034,012301,012340,012345$, including
their geometric interpretation and reversal. The $012032$ share-16
requirement is established. The completed baseline profile needs none
of these additional share assumptions and currently recovers 235.'''+ '"""'+''')
'''
s=s.replace(needle,addition+needle)
target=prior.with_name('update_paper_after153.py');assert not target.exists()
compile(s,str(target),'exec');target.write_text(s,encoding='utf-8',newline='\n')
(H/'data/future152-paper-update.json').write_text(json.dumps(dict(status='PREPARED_GUARDED152_UPDATE_FOR153_PAPER',
    source=str(prior),source_sha256=sha(prior.read_bytes()),target=str(target),target_sha256=sha(target.read_bytes()),
    baseline_paper_sha256=sha(out),executed=False),indent=2)+'\n',encoding='utf-8')
print(json.dumps({k:v for k,v in record.items() if k not in ['prose_replacements','added_bibliography_entry']}))
