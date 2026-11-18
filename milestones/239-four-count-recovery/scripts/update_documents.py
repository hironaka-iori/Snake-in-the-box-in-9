from pathlib import Path
import json
H=Path(__file__).resolve().parents[1];R=H.parents[1];D=Path('D:/Codex/2026-10-13/new-chat/outputs')
assert json.loads((H/'data/matrices-replay.json').read_bytes())['status']=='PASS'
assert json.loads((H/'data/EightCountDominance239-audit.json').read_bytes())['status']=='PASS'
def once(s,a,b):
 assert s.count(a)==1,a[:120]
 return s.replace(a,b,1)
main=(D/'snake9_research.tex').read_text(encoding='utf-8');short=(D/'snake9_frontier_explanation.tex').read_text(encoding='utf-8')
addition=(H/'paper-addition.tex').read_text(encoding='utf-8');addition=addition[addition.index(r'\subsection{'):]
small=(H/'short-addition.tex').read_text(encoding='utf-8');small=small[small.index(r'\section{'):]
addition=once(addition,'cube inverse, parity and the displayed scalar inequality. Its geometric','cube inverse, parity and the displayed scalar inequality. The supporting\ninteger list-sum and even-row inequalities have also passed Lean; their\napplication to the missing cube positions remains written. Its geometric')
small=once(small,'so $M=0$. This is a written deduction from the inverse. The condition','so $M=0$. The supporting integer inequalities passed Lean; their\napplication to the cube remains a written deduction. The condition')
main=once(main,'number of altered counts remains between four and nine. The next\nquestion is whether four missing observations can also be tolerated.','number of altered counts is at this stage between four and nine.\nSection~\\ref{sec:four-erasure239} strengthens the lower threshold to five.')
main=once(main,r'\section{A numerical conjecture and its limitations}',addition+'\n'+r'\section{A numerical conjecture and its limitations}')
main=once(main,'191-edge seed, under the stated finite and native evidence.','191-edge seed, under the stated finite and native evidence.\nNeighbour-count reconstruction tolerates four arbitrary missing\nobservations, and eight when no missing pair has Hamming distance eight.\nThe geometric deductions, their checked arithmetic, and the remaining\nproof-assistant assembly are identified separately.')
short=once(short,'Research continues\nthrough rounds 238 and 239 as requested.','The following sections develop the reconstruction argument further.')
short=once(short,'Whether four missing counts are also recoverable is the next question.','The following section extends this conclusion to four missing counts.')
short=once(short,r'\section{Remaining questions}',small+'\n'+r'\section{Remaining questions}')
short=once(short,'Resolving the proposed value 196 still requires both its witness and\na universal 197-edge exclusion.','Resolving the proposed value 196 still requires both its witness and\na universal 197-edge exclusion. For reconstruction, the next unresolved\ncase has five missing positions of one parity containing a distance-eight\npair. Fixing that pair by cube symmetry reduces a complete description\ncover to $\\binom{15}{7}=6435$ coordinate-column multiplicities. This\nreduction is proposed for the next investigation; it has not been searched.\nResearch is paused after round 239.')
summary='The current reconstruction argument recovers a binary selection from\nany 508 labelled neighbour counts. It also permits up to eight missing\ncounts when no pair of missing positions is at distance eight. These\nare written cube deductions with checked arithmetic; the fully assembled\nLean cube theorem currently covers three missing counts.\n\n'
short=once(short,r'\section{The square budget and the completed upper bound}',summary+r'\section{The square budget and the completed upper bound}')
bib=r'''\bibitem{research239}
I.~Hironaka, T.~Ma, and S.~Zhan. \emph{Four missing neighbour counts and a
conditional eight-count theorem}. Research milestone 239, 18 November 2026.
\url{https://github.com/hironaka-iori/Snake-in-the-box-in-9/tree/main/milestones/239-four-count-recovery}.

'''
for name,s in [('snake9_research.tex',main),('snake9_frontier_explanation.tex',short)]:
 assert r'\bibitem{research239}' not in s
 s=s.replace('Research state after round 238','Research state after round 239').replace('milestones through round 238','milestones through round 239')
 s=once(s,r'\end{thebibliography}',bib+r'\end{thebibliography}')
 (D/name).write_text(s,encoding='utf-8',newline='\n');(R/'paper'/name).write_bytes((D/name).read_bytes());print('UPDATED',name)
