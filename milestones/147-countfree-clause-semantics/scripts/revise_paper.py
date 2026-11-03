"""Update only verification status and its evidence reference."""
from pathlib import Path
import hashlib,json,re
H=Path(__file__).resolve().parents[1];R=H.parents[1]
paper=R/'paper/snake9_research.tex';editor=Path('D:/Codex/2026-10-13/new-chat/outputs/snake9_research.tex')
sha=lambda b:hashlib.sha256(b).hexdigest()
raw=editor.read_bytes();assert raw==paper.read_bytes()
assert sha(raw)=='3485d6c9c4e195a408b271c2d4ab4092c5b54f775473e0d7f0e3173be37258fb'
old=raw.decode('utf-8');s=old
before=r'''The $012301$ share-16 target has a complete independent Boolean replay of
285541 deductions and 31017505 propagation references from 12977 original
core clauses. Its complete Lean replay, cycle-clause interpretation,
coordinate transfer and reversal remain required~\cite{share145archive}.'''
after=r'''The $012301$ share-16 target has a complete independent Boolean replay of
285541 deductions and 31017505 propagation references from 12977 original
core clauses~\cite{share145archive}. The interpretation of every core clause
has now been checked in Lean under the local path, endpoint and share-cap
premises. This includes all six retained induced-eight-cycle exclusions,
which follow from acyclicity. The composed implication from a contradiction
of this exact core to the local share bound is also checked. The contradiction
remains a premise of that implication. A separate 36-module replay pilot
connects the original core to the initial proof state and checks the first
1030 deductions, 6004 propagation references and a complete checkpoint.
The complete Lean replay, coordinate transfer and reversal remain required
~\cite{semantics147archive}.'''
assert s.count(before)==1;s=s.replace(before,after)
bib=r'''\bibitem{semantics147archive}
I.~Hironaka, T.~Ma, and S.~Zhan. \emph{Complete clause interpretation and a
checked replay pilot for the 012301 share certificate}. Research record 147,
4 November 2026. Local research records:
\path{milestones/147-countfree-clause-semantics/data/semantics-completion.json}
and \path{milestones/147-countfree-clause-semantics/replay/data/pilot-completion.json}.
The complete contradiction and its application to arbitrary snakes remain pending.

'''
assert s.count('\\end{thebibliography}')==1;s=s.replace('\\end{thebibliography}',bib+'\\end{thebibliography}')
assert s.split('\\begin{document}',1)[0]==old.split('\\begin{document}',1)[0]
assert '.lean' not in s
assert s.count('\\begin{definition}')==old.count('\\begin{definition}')==1
for env in ['theorem','proposition','lemma','corollary','definition','equation','align','quote','longtable']:
    pattern=r'\\begin\{'+env+r'\*?\}[\s\S]*?\\end\{'+env+r'\*?\}'
    assert re.findall(pattern,s)==re.findall(pattern,old),env
assert re.findall(r'\\\[[\s\S]*?\\\]',s)==re.findall(r'\\\[[\s\S]*?\\\]',old)
backup=H/'audit/paper-before147.tex.txt';assert not backup.exists();backup.write_bytes(raw)
new=s.encode('utf-8');editor.write_bytes(new);paper.write_bytes(new)
assert editor.read_bytes()==paper.read_bytes()==new
record=dict(status='PASS_TARGETED_VERIFICATION_STATUS_REVISION',revision=147,full_revision=False,
    source_sha256_before=sha(raw),source_sha256_after=sha(new),preamble_and_authors_unchanged=True,
    mathematical_statements_and_displays_unchanged=True,definition_environment_count=1,
    exact_replacement_before=before,exact_replacement_after=after,added_bibliography_entry=bib,
    last_full_revision=146,next_full_revision=156)
(H/'data/paper-revision.json').write_text(json.dumps(record,indent=2)+'\n',encoding='utf-8',newline='\n')
print(json.dumps({k:record[k] for k in ['status','source_sha256_after','definition_environment_count']}))
