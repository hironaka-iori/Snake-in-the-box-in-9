"""Update mathematical claims only after the complete actual-snake check passes."""
from pathlib import Path
import hashlib, json
H=Path(__file__).resolve().parents[1]; R=H.parents[1]
read=lambda p:json.loads(p.read_text(encoding='utf-8-sig'))
sha=lambda b:hashlib.sha256(b).hexdigest()
completed=read(H/'data/actual-snake-completion.json')
assert completed['status']=='PASS_UNCONDITIONAL_012032_SHARE16'
assert completed['new_global_upper_bound'] is False
paper=R/'paper/snake9_research.tex'
editor=Path('D:/Codex/2026-10-13/new-chat/outputs/snake9_research.tex')
raw=paper.read_bytes(); assert raw==editor.read_bytes()
assert sha(raw)=='4d4c7a43d188d05bef483f30e4c55892cceb45b1978f2a6e4d188927eb262bcd'
old=raw.decode('utf-8'); new=old; changes=[]

def replace(before,after):
    global new
    assert new.count(before)==1,(before,new.count(before))
    new=new.replace(before,after)
    changes.append(dict(before=before,after=after))

replace('For a six-transition segment with shape $012031$, $012304$, or $012314$, one has $H\\ge16$.',
        'For a six-transition segment with shape $012031$, $012032$, $012304$, or $012314$, one has $H\\ge16$.')
replace('For each of the first three shapes, adjoining $H\\le15$',
        'For each of the first four shapes, adjoining $H\\le15$')
replace(r'give the stated bounds~\cite{countfreearchive,shareclosurearchive}.',
        r'give the stated bounds~\cite{countfreearchive,shareclosurearchive,share152archive}.')
replace(r'$012032$ & 16 & Pending\\',r'$012032$ & 16 & Checked\\')
replace(r'''All nine target formulas have independently checked native Boolean refutations. Five still lack a completed Lean chain through the contradiction and geometric interpretation. The $012310$ target now has a completed contradiction replay, arbitrary-coordinate interpretation and reversal. Five local shapes therefore remain unresolved. The current conditional argument uses floor 18 for $012034$ and the displayed targets for the other four pending shapes. The classification and conditional combination are checked separately from those premises. For $012034$, clause interpretation has passed, while the contradiction replay and target share theorem remain incomplete~\cite{shareclosurearchive,targetsharearchive}.''',
        r'''All nine target formulas have independently checked native Boolean refutations. Four still lack a completed Lean chain through the contradiction and geometric interpretation: $012034$, $012301$, $012340$ and $012345$. The $012032$ share-16 bound now has a complete contradiction replay, arbitrary-coordinate interpretation and reversal. The current conditional argument requires floor 18 for $012034$ and floor 16 for the other three pending shapes. The classification and conditional combination are checked separately from those premises. For $012034$, clause interpretation has passed, while the contradiction replay and target share theorem remain incomplete~\cite{shareclosurearchive,targetsharearchive,share152archive}.''')
replace('Allow only the five unfinished floors to decrease to',
        'Allow only the five selected floors to decrease to')
replace(r'''The conditional 234 profile additionally requires share floors
$(16,18,16,16,16)$ for $012032,012034,012301,012340,012345$ and has a
strict margin of 30 at length 235 under those premises
~\cite{referenceunionarchive,potentialcertificatearchive}.''',
        r'''The conditional 234 profile uses share floors
$(16,18,16,16,16)$ for $012032,012034,012301,012340,012345$ and has a
strict margin of 30 at length 235 under those premises. The $012032$
floor is now established; the remaining four floors and the separate
reference and potential obligations remain
~\cite{referenceunionarchive,potentialcertificatearchive,share152archive}.''')
replace(r'''All core-clause interpretations and the actual-snake transfer have passed
Lean in 112 modules. Conditional on a contradiction of this exact core,
every fitting window whose forward or reversed canonical directions are
$012032$ satisfies
\[
\sum_{j=1}^{5}\sigma_{12}(x_{r+j})\ge16.
\]
No additional count, parity or endpoint-location hypothesis is required.
The complete numerical proof has also been transported to a packed replay
with 878 segments. A 38-module pilot now connects the exact core to the
initial replay state and checks 2169 deductions with 6151 propagation
references. The first 32-segment block extends the checked prefix to
3728 deductions and 195386 references, including its checkpoint transfer.
There are 49 accepted modules among the 342 prepared for the full replay.
The final contradiction remains uncompleted and is still an explicit
premise of the actual-snake share bound~\cite{share150archive,pilot151archive}.''',
        r'''The 112 core-clause interpretation and geometric-transfer modules are
checked. All 342 modules of the complete contradiction replay have now
passed Lean, covering the 878 segments and ending in the empty clause.
Composing these results proves that every fitting window whose forward
or reversed canonical directions are $012032$ satisfies
\[
\sum_{j=1}^{5}\sigma_{12}(x_{r+j})\ge16.
\]
The final actual-snake composition has also passed Lean. There is no
remaining contradiction premise or additional count, parity or
endpoint-location hypothesis. Exact sources, compiled objects and saved
dependency records were checked; the inherited coordinate machinery
includes one previously compiled data object, and the external Lean and
mathematics libraries remain trusted. This completes the $012032$ case
of Theorem~\ref{thm:countfree-completed}, while the other four target
shapes remain unresolved~\cite{share150archive,pilot151archive,share152archive}.''')
replace('whereas the proposed $012032$ floor 16 raises its',
        'whereas the established $012032$ floor 16 raises its')
bib=r'''\bibitem{share152archive}
I.~Hironaka, T.~Ma, and S.~Zhan, \emph{Complete count-independent share
bound for the 012032 window}, research archive, milestone 152.
\url{https://github.com/hironaka-iori/Snake-in-the-box-in-9/tree/main/milestones/152-countfree-share16-completion}.

'''
replace(r'\end{thebibliography}',bib+r'\end{thebibliography}')
assert old.split(r'\begin{document}',1)[0]==new.split(r'\begin{document}',1)[0]
assert old.count(r'\begin{definition}')==new.count(r'\begin{definition}')
assert '.lean' not in new
backup=H/'audit/paper-before152.tex.txt'; assert not backup.exists(); backup.write_bytes(raw)
out=new.encode('utf-8');paper.write_bytes(out);editor.write_bytes(out)
record=dict(status='PASS_COMPLETE_SHARE16_PAPER_REVISION',source_sha256_before=sha(raw),
            source_sha256_after=sha(out),prose_replacements=changes,
            authors_and_preamble_unchanged=True,new_definitions=0,last_full_revision=146,next_full_revision=156)
(H/'data/paper-revision.json').write_text(json.dumps(record,indent=2)+'\n',encoding='utf-8')
print(json.dumps({k:v for k,v in record.items() if k!='prose_replacements'}))
