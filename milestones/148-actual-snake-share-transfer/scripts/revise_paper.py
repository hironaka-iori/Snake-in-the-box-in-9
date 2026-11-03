"""Record the checked actual-snake implication, retaining its contradiction premise."""
from pathlib import Path
import hashlib,json,re
H=Path(__file__).resolve().parents[1];R=H.parents[1]
paper=R/'paper/snake9_research.tex';editor=Path('D:/Codex/2026-10-13/new-chat/outputs/snake9_research.tex')
sha=lambda b:hashlib.sha256(b).hexdigest()
receipt=json.loads((H/'data/transfer-completion.json').read_text())
assert receipt['status']=='PASS_CONDITIONAL_ACTUAL_SNAKE_SHARE16_TRANSFER'
raw=editor.read_bytes();assert raw==paper.read_bytes()
assert sha(raw)=='8adf5c2b0727aa95f121cb705603206acc13bff2adb4ed4f97db358a5580864b'
old=raw.decode('utf-8');s=old
before=r'''The complete Lean replay, coordinate transfer and reversal remain required
~\cite{semantics147archive}.'''
after=r'''The coordinate and reversal transfer is now checked conditional on a
contradiction of this exact core. For every fitting six-transition window
whose forward or reversed canonical directions are $012301$, it gives
$\sum_{j=1}^{5}\sigma_{12}(x_{r+j})\ge16$. The universal count bounds are
sufficient; no additional count, parity or endpoint-location premise is
imposed. Completion of the full Lean replay remains necessary to discharge
the contradiction premise~\cite{semantics147archive,transfer148archive}.'''
assert s.count(before)==1;s=s.replace(before,after)
bib=r'''\bibitem{transfer148archive}
I.~Hironaka, T.~Ma, and S.~Zhan. \emph{The actual-snake consequence of the
012301 core refutation}. Research record 148, 4 November 2026.
Local research record:
\path{milestones/148-actual-snake-share-transfer/data/transfer-completion.json}.
The forward and reversed consequences are checked with the contradiction
premise retained. One earlier automaton data object is reused with matched
source, object and dependency hashes.

'''
assert s.count('\\end{thebibliography}')==1;s=s.replace('\\end{thebibliography}',bib+'\\end{thebibliography}')
assert s.split('\\begin{document}',1)[0]==old.split('\\begin{document}',1)[0]
assert '.lean' not in s and s.count('\\begin{definition}')==old.count('\\begin{definition}')==1
for env in ['theorem','proposition','lemma','corollary','definition','equation','align','quote','longtable']:
    pattern=r'\\begin\{'+env+r'\*?\}[\s\S]*?\\end\{'+env+r'\*?\}'
    assert re.findall(pattern,s)==re.findall(pattern,old),env
assert re.findall(r'\\\[[\s\S]*?\\\]',s)==re.findall(r'\\\[[\s\S]*?\\\]',old)
backup=H/'audit/paper-before148.tex.txt';assert not backup.exists();backup.write_bytes(raw)
new=s.encode('utf-8');editor.write_bytes(new);paper.write_bytes(new)
assert editor.read_bytes()==paper.read_bytes()==new
out=dict(status='PASS_TARGETED_CONDITIONAL_TRANSFER_PAPER_REVISION',revision=148,full_revision=False,
    source_sha256_before=sha(raw),source_sha256_after=sha(new),preamble_and_authors_unchanged=True,
    existing_mathematical_statements_and_displays_unchanged=True,new_definitions=0,
    exact_replacement_before=before,exact_replacement_after=after,added_bibliography_entry=bib,
    last_full_revision=146,next_full_revision=156,transfer_receipt_sha256=sha((H/'data/transfer-completion.json').read_bytes()))
(H/'data/paper-revision.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8',newline='\n')
print(json.dumps({k:out[k] for k in ['status','source_sha256_after','new_definitions']}))
