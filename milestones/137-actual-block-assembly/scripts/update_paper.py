"""Add the completed occurrence theorem to the existing editor document."""
from pathlib import Path
import hashlib,json
H=Path(__file__).resolve().parents[1];R=H.parents[1]
P=Path('D:/Codex/2026-10-13/new-chat/outputs/snake9_research.tex')
sha=lambda b:hashlib.sha256(b).hexdigest()
old=P.read_bytes();assert sha(old)=='820820fafd255800cfe60f3c6cdde53dccc333ccaea2a49255299616458b1b0c'
assert old==(R/'paper/snake9_research.tex').read_bytes()
receipt=json.loads((H/'data/ActualCount137-audit.json').read_text())
assert receipt['status']=='PASS' and len(receipt['axioms'])==4
assert sha((H/'lean/ActualCount137.lean').read_bytes())==receipt['source_sha256']
(H/'audit/paper-before.tex.txt').write_bytes(old)
s=old.decode('utf-8')
def replace(a,b):
 global s
 assert s.count(a)==1,(a,s.count(a))
 s=s.replace(a,b)
replace('We prove that at most thirty-two such windows occur in any snake, allowing overlap and either length parity.',
        'We prove that at most twenty-four such windows occur in any snake, allowing overlap and either length parity.')
replace(' A stronger twenty-four-window estimate remains under verification.','')
replace('Low-pair occurrence bound & At most thirty-two $012032$ windows have pair sum at most nine. The proposed total twenty-four remains under verification.',
        'Low-pair occurrence bound & At most twenty-four $012032$ windows have pair sum at most nine, with at most twelve assigned to either endpoint.')
replace('\\subsection{Missing pairs and the proposed stronger count}',
        '\\subsection{Missing pairs and the stronger occurrence bound}')
start=s.index('A consecutive-block construction is also checked:')
end=s.index('\\subsection{Necessary counts in an unresolved seven-transition window}',start)
s=s[:start]+(H/'audit/paper-count-proof.tex.txt').read_text(encoding='utf-8')+'\n'+s[end:]
replace('the parity-free endpoint consequence and the thirty-two-window bound are',
        'the parity-free endpoint consequence and the twenty-four-window bound are')
replace('nor the completed endpoint-equality and thirty-two-window theorems lower',
        'nor the completed endpoint-equality and twenty-four-window theorems lower')
entry='''\\bibitem{count24archive}
I.~Hironaka, T.~Ma, and S.~Zhan. \\emph{Actual interval counts and a checked bound of twenty-four low-pair windows}. Research record 137, 3 November 2026.
\\url{https://github.com/hironaka-iori/Snake-in-the-box-in-9/tree/main/milestones/137-actual-block-assembly}.

'''
replace('\\end{thebibliography}',entry+'\\end{thebibliography}')
b=s.encode('utf-8')
assert b.split(b'\\begin{document}',1)[0]==old.split(b'\\begin{document}',1)[0]
assert b.count(b'\\begin{definition}')==old.count(b'\\begin{definition}')
assert b'.lean' not in b
P.write_bytes(b);(R/'paper/snake9_research.tex').write_bytes(b)
j=dict(status='SAVED_TARGETED_UPDATE137_AWAITING_COMPILER',before_sha256=sha(old),after_sha256=sha(b),
 editor=str(P),repository=str(R/'paper/snake9_research.tex'),authors_and_preamble_unchanged=True,
 new_named_definitions=0,checked_per_endpoint_bound=12,checked_total_bound=24,
 stronger_boundary_free_eleven_checked=False,new_global_length_bound=False,
 last_full_paper_revision=136,targeted_paper_update=137,next_full_paper_revision=146)
(H/'data/paper-revision.json').write_text(json.dumps(j,indent=2)+'\n',encoding='utf-8')
print(json.dumps(j))
