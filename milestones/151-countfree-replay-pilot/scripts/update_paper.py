"""Update verification scope after the exact initial tree and first32 segments pass."""
from pathlib import Path
import hashlib,json
H=Path(__file__).resolve().parents[1];R=H.parents[1]
read=lambda p:json.loads(p.read_text(encoding='utf-8-sig'))
assert read(H/'data/first-group-completion.json')['status']=='PASS_FIRST32_REPLAY_SEGMENTS_AND_CHECKPOINT'
paper=R/'paper/snake9_research.tex';editor=Path('D:/Codex/2026-10-13/new-chat/outputs/snake9_research.tex')
raw=paper.read_bytes();assert raw==editor.read_bytes()
sha=lambda b:hashlib.sha256(b).hexdigest()
assert sha(raw)=='23a76016133a77cbfc439a7429274ca7aea5b216f8fe2e3e72f2432c950a69a1'
old=raw.decode('utf-8')
before=r'''The complete numerical proof has also been transported to a packed replay
with 878 segments. Its initial-tree and prefix sources are prepared; they
have not yet been checked in Lean. The full contradiction therefore remains
an explicit premise, and this target is still among the uncompleted local
share theorems~\cite{share150archive}.'''
after=r'''The complete numerical proof has also been transported to a packed replay
with 878 segments. A 38-module pilot now connects the exact core to the
initial replay state and checks 2169 deductions with 6151 propagation
references. The first 32-segment block extends the checked prefix to
3728 deductions and 195386 references, including its checkpoint transfer.
There are 49 accepted modules among the 342 prepared for the full replay.
The final contradiction remains uncompleted and is still an explicit
premise of the actual-snake share bound~\cite{share150archive,pilot151archive}.'''
assert old.count(before)==1
bib=r'''\bibitem{pilot151archive}
I.~Hironaka, T.~Ma, and S.~Zhan, \emph{Initial-state connection and bounded
replay of the count-free 012032 certificate}, research archive, milestone 151.
\url{https://github.com/hironaka-iori/Snake-in-the-box-in-9/tree/main/milestones/151-countfree-replay-pilot}.

'''
new=old.replace(before,after).replace(r'\end{thebibliography}',bib+r'\end{thebibliography}')
assert old.split(r'\begin{document}',1)[0]==new.split(r'\begin{document}',1)[0]
assert old.count(r'\begin{definition}')==new.count(r'\begin{definition}') and '.lean' not in new
backup=H/'audit/paper-before151.tex.txt';backup.parent.mkdir(exist_ok=True);assert not backup.exists();backup.write_bytes(raw)
out=new.encode('utf-8');paper.write_bytes(out);editor.write_bytes(out)
record=dict(status='PASS_TARGETED_REPLAY_VERIFICATION_REVISION',source_sha256_before=sha(raw),source_sha256_after=sha(out),
    prose_replacements=[dict(before=before,after=after)],added_bibliography_entry=bib,
    authors_and_preamble_unchanged=True,new_definitions=0,last_full_revision=146,next_full_revision=156)
(H/'data/paper-revision.json').write_text(json.dumps(record,indent=2)+'\n',encoding='utf-8')
print(json.dumps({k:v for k,v in record.items() if k not in ['prose_replacements','added_bibliography_entry']}))
