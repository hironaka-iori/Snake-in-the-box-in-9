"""Revise the existing editor source in place and synchronize the repository copy."""
from pathlib import Path
import hashlib,json,re,textwrap
H=Path(__file__).resolve().parents[1];R=H.parents[1]
editor=Path('D:/Codex/2026-10-13/new-chat/outputs/snake9_research.tex')
repo=R/'paper/snake9_research.tex'
sha=lambda b:hashlib.sha256(b).hexdigest()
before=editor.read_bytes();assert repo.read_bytes()==before
assert sha(before)=='4667daec19f0b83af9fb129a263c8ae992757105414bad817c1ad13e1e11bb90'
(H/'audit/paper-before.tex.txt').write_bytes(before)
s=before.decode('utf-8');prefix=s.split('\\begin{document}',1)[0]
def once(old,new):
 global s
 assert s.count(old)==1,old[:120]
 s=s.replace(old,new,1)
def fragment(name):return (H/'audit'/name).read_text(encoding='utf-8')
abstract=r'''Let $a(9)$ denote the maximum edge length of an induced path in the nine-dimensional binary hypercube. An explicit construction and an archived contributor proof give $191\le a(9)\le235$; a complete independent rebuild of the upper-bound proof remains pending. Writing $m$ for the edge length, $T$ for the total singleton-square count and $s_0$ for the empty-square count, the identity is $T+2s_0+35(m+1)=9214$. For a canonical $012032$ window, the second and fourth internal counts have sum at least eight. Equality forces both endpoints into the common distance-two sphere and can occur at most thirteen times; it also requires an even path length and an even window start. A sum at most nine forces an endpoint to share an unselected neighbour with the four alternate window vertices. We prove that at most thirty-two such windows occur in any snake, allowing overlap and either length parity. Explicit odd-length snakes show that a uniform pair floor ten is false. Six-count and empty-square criteria give conditional improvements to 234 and 233, while surviving cycles limit the tested finite comparisons. A stronger twenty-four-window estimate remains under verification. The optimum and the numerical conjecture 196 remain unresolved.'''
s=re.sub(r'(?s)(\\begin\{abstract\}\n).*?(\n\\end\{abstract\})',lambda m:m[1]+abstract+m[2],s,count=1)
once('New local count restrictions & The six-count floor 25 is proved for $0123041$. The $012032$ pair bound eight is sharp; $0120324$ has a checked necessary interval restriction.\\\\',
 'New local count restrictions & The six-count floor 25 is proved for $0123041$. On $0120324$, fourth count three forces a six-count sum at least 23.\\\\\n'
 'Endpoint and parity restrictions & Pair sum eight on $012032$ forces both endpoints into the common sphere, at most thirteen occurrences, and even path length and start.\\\\\n'
 'Low-pair occurrence bound & At most thirty-two $012032$ windows have pair sum at most nine. The proposed total twenty-four remains under verification.\\\\')
a=s.index('For this pattern, the case $(2,6)$ also forces both endpoints')
b=s.index('\\subsection{Necessary counts in an unresolved seven-transition window}',a)
s=s[:a]+fragment('pair-section.tex.txt')+'\n'+s[b:]
marker='\\subsection{Necessary counts in an unresolved seven-transition window}\\label{sec:critical-six}\n'
once(marker,marker+fragment('fourth-count.tex.txt')+'\n')
once('([1,21],[2,21],[1,21],[3,21],[1,21],[1,21]).',
 '([1,21],[2,21],[1,21],[4,21],[1,21],[1,21]).')
once('Consequently $\\alpha_{r+4}\\ge3$. Positivity and the internal upper bound\n21 give all other intervals. The prefix exclusion, canonical suffix\nidentification and complete deduction for arbitrary snakes have passed\nLean~\\cite{criticalsixarchive}.',
 'Consequently $\\alpha_{r+4}\\ge3$. Proposition~\\ref{prop:fourth-three-twelve}\nexcludes equality to three under the assumed total at most 22, so\n$\\alpha_{r+4}\\ge4$. Positivity and the internal upper bound 21 give the\nother intervals. The constituent exclusions and actual-snake deductions\nhave passed Lean~\\cite{criticalsixarchive,endpointcompletionarchive}.')
once('Three full-cube searches for totals at most 24, at most 22, and at most 22',
 'Three earlier full-cube searches for totals at most 24, at most 22, and at most 22')
once('establish no additional count floor~\\cite{criticalsixarchive}.',
 'establish no additional count floor~\\cite{criticalsixarchive}. The later\nfourth-count-three result closes that case, while the complementary case\n$\\alpha_{r+4}\\ge4$ remains unresolved. Subsequent encoding changes and\npartial deductions provide no exclusion of this complementary case.')
once('The latest combined experiment grants six-count floors 26, 25 and 25 on',
 'A preceding combined experiment grants six-count floors 26, 25 and 25 on')
once('\\subsection{What an integer improvement requires}',
 fragment('comparison-section.tex.txt')+'\n\\subsection{What an integer improvement requires}')
once('The later completed-share mean is also below the first threshold, since $111960\\cdot6-227\\cdot2915=10055>0$.',
 'The preceding completed-share mean is below the first threshold, since $111960\\cdot6-227\\cdot2915=10055>0$. The odd-length refinement is also below it: $111960-227\\cdot488=1184>0$.')
once('the latest attaining cycles avoid all three seven-transition shapes tested there and still leave the integer comparisons unchanged.',
 'the later attaining cycles also avoid the additional $0123104$ target and leave the integer comparisons unchanged. The endpoint-occurrence bound must additionally address the obstruction in Proposition~\\ref{prop:uniform-occurrence-credit}.')
once('nor the incomplete endpoint-equality argument lowers the maintained interval.',
 'nor the completed endpoint-equality and thirty-two-window theorems lower the maintained interval by themselves.')
once('The pair bound for $012032$, the six-count bound for $0123041$, and the\nnecessary intervals for low-total $0120324$ windows are checked for actual\nsnakes.',
 'The $012032$ pair bound, its equality geometry and parity restriction,\nthe parity-free endpoint consequence and the thirty-two-window bound are\nchecked for actual snakes. The $0123041$ six-count bound, necessary intervals\nfor low-total $0120324$ windows and fourth-count-three case are also checked.')
once('A written interval argument proposes twelve assigned windows per endpoint,',
 'A consecutive-block construction is also checked: sort the sampled starts\nand group consecutive gaps of at most two. Each block has one common coordinate,\nthe blocks partition the starts, and their expanded intervals overlap in at\nmost one position. The missing-pair finite set can now be taken directly\nfrom the actual snake; its run bound uses the actual degree and at most\n$8-|A|$ outside coordinates. Summing all these statements with the unique\nexceptional prefix remains unfinished~\\cite{intervalassemblyarchive}.\n\nA written interval argument proposes twelve assigned windows per endpoint,')
witnesses=[]
for folder,length,start,pair in [('probe-endpoint18',149,130,[6,3]),('probe-balanced',133,27,[4,5])]:
 p=R/'milestones/133-endpoint-occurrences/work'/folder/'actual-path.json'
 j=json.loads(p.read_text());v=j['ordered_path'];assert len(v)==length+1
 assert len(set(v))==len(v) and v[start:start+7]==[0,1,3,7,6,14,10]
 assert all(((v[a]^v[b]).bit_count()==1)==(b==a+1) for a in range(len(v)) for b in range(a+1,len(v)))
 dirs=''.join(str((a^b).bit_length()-1) for a,b in zip(v,v[1:]))
 assert len(dirs)==length and set(dirs)<=set('012345678')
 witnesses.append(dict(folder=folder,edges=length,start=start,pair=pair,initial=v[0],final=v[-1],directions=dirs,source_sha256=sha(p.read_bytes())))
extra=r'''\section{Odd-length witnesses attaining pair sum nine}\label{app:odd-pair-witnesses}
Both complete snakes below contain the normalized window $(0,1,3,7,6,14,10)$.
They show that nine is sharp for odd-length snakes, including when both
counts are at least four. They do not improve the 191-edge construction.

'''
for w,counts in zip(witnesses,['(8,6,10,3,8)','(11,4,13,5,12)']):
 extra+='\\subsection{The pair $('+','.join(map(str,w['pair']))+')$}\n'
 extra+=f"The snake has {w['edges']} edges, starts at vertex {w['initial']}, ends at vertex {w['final']}, and has its designated window at $r={w['start']}$. Its five internal counts are ${counts}$.\n\n"
 extra+='\\begin{quote}\\ttfamily\\small\n'+'\\\\\n'.join(textwrap.wrap(w['directions'],68))+'\n\\end{quote}\n\n'
extra+=r'''Only endpoint 18 qualifies in the first example; the window begins 130
path steps after it. Only endpoint 130 qualifies in the second; the window
begins 106 path steps before it. Hamming proximity does not imply proximity
along the path. Complete Lean checks verify both paths, their counts, window
directions and endpoint distances~\cite{oddwitnessarchive}.

'''
once('\\clearpage\n\\addcontentsline{toc}{section}{References}',extra+'\\clearpage\n\\addcontentsline{toc}{section}{References}')
once('\\end{thebibliography}',fragment('new-references.tex.txt')+'\n\\end{thebibliography}')
assert s.split('\\begin{document}',1)[0]==prefix
assert '\\author{Iori Hironaka \\and Tommy Ma \\and Steven Zhan}' in s and '.lean' not in s
after=s.encode('utf-8');editor.write_bytes(after);repo.write_bytes(after)
record=dict(status='SAVED_PAPER_REVISION136_AWAITING_COMPILE',before_sha256=sha(before),after_sha256=sha(after),
 editor=str(editor),repository=str(repo),authors_and_preamble_unchanged=True,new_named_definitions=0,
 checked_occurrence_bound=32,stronger_total24_completed=False,global_upper_improved=False,witnesses=witnesses)
(H/'data/paper-revision.json').write_text(json.dumps(record,indent=2)+'\n',encoding='utf-8')
print(json.dumps({k:v for k,v in record.items() if k!='witnesses'}))
