from pathlib import Path
import json, re, hashlib

H = Path(__file__).resolve().parents[1]
R = H.parents[1]
D = Path('D:/Codex/2026-10-13/new-chat/outputs')
assert json.loads((H/'data/matrices-replay.json').read_bytes())['status'] == 'PASS'
assert json.loads((H/'data/independent-geometry.json').read_bytes())['status'] == 'PASS_GEOMETRIC_CLASS_COVERAGE'
assert json.loads((H/'data/EightCubeObstruction240-audit.json').read_bytes())['status'] == 'PASS'

def replace(text, old, new):
    assert text.count(old) == 1, (old[:150], text.count(old))
    return text.replace(old, new)

main = (H/'data/snake9_research-before.tex').read_text(encoding='utf-8')
short = (H/'data/snake9_frontier_explanation-before.tex').read_text(encoding='utf-8')
addition = (H/'paper-addition.tex').read_text(encoding='utf-8')
addition = replace(addition, 'Completion of all 372 kernel checks is pending in\nthis draft.', 'All 372 implications have passed Lean checking, with their\nsource-bound proof receipts retained.')
addition = replace(addition, 'The native audit covers the 6435 column descriptions and the 90396\nexact arithmetic cases.', 'The native audit covers the 6435 column descriptions and the 90396\nexact arithmetic cases. An independent enumeration of all\n$\\binom{254}{3}=2699004$ triples of actual even vertices outside the\nfixed pair gives exactly the same 372 distance matrices.')
addition = '\n'.join(x for x in addition.split('\n') if not x.startswith('% Publication gate:') and not x.startswith('% only after'))
short_addition = (H/'short-addition.tex').read_text(encoding='utf-8')
short_addition = replace(short_addition, 'match the saved matrices; their complete kernel run is pending in\nthis draft.', 'match the saved matrices and all passed Lean checking. A separate\nenumeration of all 2699004 triples of actual vertices outside the fixed\npair recovers the same 372 matrix types.')
short_addition = '\n'.join(x for x in short_addition.split('\n') if not x.startswith('% Publication gate:') and not x.startswith('% complete root-worker'))

limitation = r'''
\subsection{Why later recovery arguments need the count bound}
\label{sec:eight-matrix-limit240}
The unrestricted integer conclusion of Lemma~\ref{lem:five-matrix240}
does not extend to all eight-position configurations. Let
$g_i=(1,\ldots,1)\mathbin{\oplus}e_i$, and take the eight sums of
$g_0,g_1,g_2$. In subset order they are
\[
P=(0,510,509,3,507,5,6,504),\qquad
\chi=(1,-1,-1,1,-1,1,1,-1).
\]
For their antipodal matrix $H$, the coefficients at distances zero,
one, two and three in these generator coordinates are $128,35,-16,-10$.
Therefore
\[
H\chi=(128-3\cdot35-3\cdot16+10)\chi=-15\chi,
\qquad H(21\chi)=315(-\chi).
\]
This nonzero integer solution has ternary right-hand side. Its explicit
matrix equations, vertex properties and amplitudes passed Lean checking.
However, actual neighbour-count differences obey $|w_i|\le9$, whereas
these amplitudes are 21. It is consequently no counterexample to
binary-selection recovery.

The saved structural note proves that zero and these two signed
amplitude-21 solutions are the only integer solutions for this matrix
with ternary right-hand side. The proof uses the character eigenvalues
$175,189,99,-15$, integer divisibility and inversion modulo three.
It therefore excludes this configuration under $|w_i|\le9$.
It also excludes entire-support distance-eight stars of at most eight
positions. These classifications remain written proofs; the checked
explicit matrix witness has the narrower scope stated above.
General six-, seven- and eight-position recovery remains unresolved.
Any failure in that range is supported on one parity side: if both
parity restrictions of $f$ were nonzero, Proposition~\ref{prop:five-erasure240}
would force at least six changed counts on each of the two disjoint
opposite sides, giving at least twelve in total.
Disconnected distance-eight components retain nonzero even matrix
entries between them, so a connected-component argument alone does
not settle the question~\cite{research240}.

'''
short_limit = r'''
The integer argument cannot be extended to eight positions without
further restrictions. One explicit eight-point configuration has a
nonzero integer solution whose count differences all have absolute
value 21. The displayed matrix solution passed Lean. Actual differences
of neighbour counts cannot exceed nine, so this is no recovery
counterexample. A separate written symmetry argument excludes every
nonzero solution for that configuration whose count differences are
bounded by nine. It explains why subsequent
arguments should retain the count limit or use further inverse equations.

'''
main = replace(main, 'Research state after round 239,', 'Research state after round 240,')
main = replace(main, 'Neighbour-count reconstruction tolerates four arbitrary missing', 'Neighbour-count reconstruction tolerates five arbitrary missing')
main = replace(main, 'positions, Proposition~\\ref{prop:four-erasure239} gives the established\nfour-count result. Any nonzero difference hidden at five through eight\npositions must include a distance-eight pair among those positions.', 'positions, Proposition~\\ref{prop:four-erasure239} first gives the\nfour-count result. Section~\\ref{sec:five-erasure240} extends this to five.\nAny nonzero difference hidden at six through eight positions must\ninclude a distance-eight pair among those positions.')
main = replace(main, 'nine counts, leaving the minimum number between five and nine. These', 'nine counts. At this stage the minimum is between five and nine;\nSection~\\ref{sec:five-erasure240} raises the lower value to six. These')
main = replace(main, '\\section{A numerical conjecture and its limitations}', addition+'\n'+limitation+'\\section{A numerical conjecture and its limitations}')
main = replace(main, 'Full-source reviews at rounds 220 and 230 check the written argument,\nhistorical status, dependencies and presentation. They do not rebuild the\narchived contributor chain or replay every numerical certificate.', r'''The actual-cube theorem from round 238 covers three missing counts.
Rounds 239 and 240 add 87 and 372 checked matrix implications,
respectively, with independent native geometry enumerations; their
four- and five-count cube assemblies remain written. The conditional
eight-count theorem has checked generic arithmetic and a written cube
application. The explicit eight-point matrix limitation has a separate
checked witness, with its bounded classification remaining written.
Full-source reviews at rounds 220, 230 and 240 check the written argument,
historical status, dependencies and presentation. They do not rebuild the
archived contributor chain or replay every numerical certificate.''')

short = replace(short, 'Research state after round 239', 'Research state after round 240')
short = replace(short, 'any 508 labelled neighbour counts.', 'any 507 labelled neighbour counts.')
short = replace(short, 'The preceding finite comparison gave exact\ncardinality bounds 95.955197 and 95.763979, excluding 95-edge partners.', 'The preceding finite comparison gave saved exact rational\ncardinality bounds approximately 95.955197 and 95.763979, excluding\n95-edge partners.')
short = replace(short, 'has 22; their largest exact bounds are 93.963070 and 93.984077.', 'has 22; their largest saved rational bounds are approximately\n93.963070 and 93.984077.')
short = replace(short, 'The final bounds are\n93.979475 and 93.414818.', 'The final bounds are approximately\n93.979475 and 93.414818.')
short = replace(short, 'The unrestricted result above remains four\nmissing counts; whether every set of five through eight missing counts\ncan be tolerated is unresolved. Any failure in that range must contain\na pair of missing positions at distance eight.', 'The unrestricted result at this stage covers four missing counts;\nthe following section extends it to five. Whether every set of six\nthrough eight missing counts can be tolerated remains unresolved. Any\nfailure in that range must contain a pair at distance eight.')
short = replace(short, 'possible number remains between five and nine.', 'possible number at this stage is between five and nine; the following\nsection raises the lower value to six.')
short = replace(short, '\\section{Remaining questions}', short_addition+'\n'+short_limit+'\\section{Remaining questions}')
short = replace(short, 'a universal 197-edge exclusion. For reconstruction, the next unresolved\ncase has five missing positions of one parity containing a distance-eight\npair. Fixing that pair by cube symmetry reduces a complete description\ncover to $\\binom{15}{7}=6435$ coordinate-column multiplicities. This\nreduction is proposed for the next investigation; it has not been searched.\nResearch is paused after round 239.', 'a universal 197-edge exclusion. For reconstruction, the next unresolved\nsizes are six through eight missing counts. The structural note reduces\neach connected distance-eight component to generator coordinates in a\nsmaller cube. A complete argument must retain actual count bounds and\naccount for nonzero couplings between disconnected components. Completing\nthe cube-level Lean assembly for four and five missing counts is also\nvaluable. Full written-source review was completed in round 240.\nResearch is paused after round 240.')
short = replace(short, 'milestones through round 239.', 'milestones through round 240.')
bib = r'''\bibitem{research240}
I.~Hironaka, T.~Ma and S.~Zhan, \emph{Five-count recovery and structural
limits of the antipodal matrix method}. Research milestone 240,
18 November 2026.
\url{https://github.com/hironaka-iori/Snake-in-the-box-in-9/tree/main/milestones/240-five-count-recovery}.

'''
for name, text in [('snake9_research', main), ('snake9_frontier_explanation', short)]:
    text = replace(text, '\\end{thebibliography}', bib+'\\end{thebibliography}')
    before = (H/'data'/(name+'-before.tex')).read_text(encoding='utf-8')
    original = D/(name+'.tex')
    assert original.read_text(encoding='utf-8') == before, 'Original changed during research'
    assert re.findall(r'\\author\{[^\n]*', text) == re.findall(r'\\author\{[^\n]*', before)
    if name == 'snake9_research':
        assert text[text.index('\\hypersetup{'):text.index('\\usepackage{microtype}')] == before[before.index('\\hypersetup{'):before.index('\\usepackage{microtype}')]
    original.write_text(text, encoding='utf-8', newline='\n')
    (R/'paper'/(name+'.tex')).write_bytes(original.read_bytes())
    print(name, len(text.splitlines()), hashlib.sha256(original.read_bytes()).hexdigest())
(H/'paper-addition.tex').write_text(addition, encoding='utf-8', newline='\n')
(H/'short-addition.tex').write_text(short_addition, encoding='utf-8', newline='\n')
