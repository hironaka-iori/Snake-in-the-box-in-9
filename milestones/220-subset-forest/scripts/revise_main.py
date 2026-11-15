from pathlib import Path
import re,json
H=Path(__file__).resolve().parents[1];R=H.parents[1]
p=Path('D:/Codex/2026-10-13/new-chat/outputs/snake9_research.tex')
old=(H/'data/before-snake9_research.tex').read_text(encoding='utf-8');assert p.read_text(encoding='utf-8')==old
s=old;changes=[]
def replace(a,b,label):
 global s
 assert s.count(a)==1,(label,s.count(a));s=s.replace(a,b);changes.append(label)
replace('Research state after round 219, 15 November 2026','Research state after round 220, 15 November 2026','Research date')
replace('bound directly. Together with Theorem~\\ref{thm:lower}, this proves\nTheorem~\\ref{thm:main}, with the archived-proof qualification already stated.','bound directly. This completes the archived upper bound 235. The stronger\nupper bound in Theorem~\\ref{thm:main} is supplied by the separate\ncontributor argument in Section~\\ref{sec:bound233}.','Correct historical proof reference')
replace('the numerical length upper bound remains 235.','the numerical conclusion of this archived count-only argument remains 235.','Historical count-only status')
replace('premises remain unresolved; consequently this does not exclude a\n235-edge snake unconditionally.','premises remain unresolved, so this alternative argument does not\nindependently supply that exclusion.','Separate alternative exclusion premises')
replace('For the completed floor choice, every fitting window of a snake satisfies','For the archived baseline floor choice, every fitting window of a snake satisfies','Name baseline floor in theorem')
replace('Use either the completed floors, or the conditional floors under their five\nlocal share premises.','Use either the archived baseline floors, or the conditional floors under\nthe five stated local bounds, four of which remain unresolved.','Name baseline and pending floors in corollary')
replace('With the completed floors, $(p,R)=(483,551)$ implies $m\\le235$.','With the archived baseline floors, $(p,R)=(483,551)$ implies $m\\le235$.','Baseline numerical substitution')
replace('The same statements hold for the conditional floor choice under the five\nlocal share bounds just stated.','The same statements hold for the conditional floor choice under the five\nstated local bounds, four of which remain unresolved.','Explicit floor status')
replace('used for the saved critical cycles. That graph already requires\n$\\alpha_{r+2}+\\alpha_{r+4}\\ge9$ in this context. Together with\n$\\alpha_{r+2}\\le4$ and $\\alpha_{r+4}\\le5$, this forces the two counts\nto equal 4 and 5.','used for the saved critical cycles. Its retained rows require the two\nstored count symbols to sum to at least nine. The tested caps are four\nand five, so both symbols are unsaturated and must equal four and five.\nFor an actual snake tracing such a row, the corresponding actual counts\ntherefore have those same values.','Distinguish stored and actual counts')
replace('Together with the maintained upper bound 235, it suffices to exclude\nlength 235. Its odd parity supplies this particular graph premise;\nthe other premises still require proof.','In this earlier argument, the archived upper bound 235 reduced the task\nto excluding length 235. Its odd parity supplies this particular graph\npremise; the other premises remain explicit.','Historical parity reduction')
replace('Clearing denominators by 2520 gives $A=2520S+B$, with $B\\le1008$,\nso $A>36288$ implies $S\\ge15$. These arithmetic statements pass Lean.','After multiplication by 2520, the rational share exceeds 36288 and the\nrounding deficit is at most 1008. The scaled integer share therefore\nexceeds $36288-1008=35280=2520\\cdot14$, so the integer share is at least\nfifteen. These arithmetic implications pass Lean.','Remove undefined rounding symbols')
replace('W+1680=120B+\\sum_iL_i+120\\cdot14\\le120T+5\\Sigma=5G_{12}.','W+1680=120B+\\sum_iH_i+120\\cdot14\\le120T+5\\Sigma=5G_{12}.','Correct five-window summand')
replace('connectivity or parity obstruction to a 93-edge partner. The next\nsearch will consider all such partners, using selected-vertex degree\nconditions and cycle exclusions as an alternative to the earlier\ncircuit formulation. Its runtime advantage is unproved.','connectivity or parity obstruction to a 93-edge partner.\nSection~\\ref{sec:partner218} reports the subsequent degree-and-cycle\nqueries. They leave both endpoints unresolved, and no runtime advantage\nover the earlier circuit formulation is established.','Link executed direct searches')
replace('indicate the free endpoint; $e_u=0$ at even vertices other than the root.','indicate the free endpoint; extend $e_u$ by zero at every even vertex,\nincluding the root.','Complete endpoint-indicator convention')
replace('edge formulation admits a selection of exactly 94 vertices satisfying\nevery simple-cycle occupancy inequality.','edge formulation admits a fractional assignment with total selection\nweight exactly 94, satisfying every simple-cycle occupancy inequality.','Make fractional feasibility unambiguous')
replace('Exact fractional certificates show that the fixed-parent degree\nformulation, even with every simple-cycle occupancy inequality,\ncannot exclude the 94-vertex compatible-partner target.','Exact fractional certificates show that the fixed-parent degree\nformulation, even with every cycle occupancy and subset forest inequality,\ncannot exclude the 94-vertex compatible-partner target. The subset\ninequalities nevertheless give exact certificates excluding a 97-edge\npartner for this representative. Explicit failures of Boolean product\nconsistency identify a further class of valid inequalities.','Current abstract')
start=s.index('The next candidate strengthening uses arbitrary vertex subsets $U$.');end=s.index('\\section{Verification scope and remaining problem}',start)
s=s[:start]+(H/'scripts/main_new_body.txt').read_text(encoding='utf-8')+'\n'+s[end:];changes.append('Replace proposed forest route with completed result')
start=s.index('\\paragraph{Construction and history verification.}');end=s.index('\\appendix',start)
s=s[:start]+(H/'scripts/construction_status.txt').read_text(encoding='utf-8')+'\n'+s[end:];changes.append('Consolidate construction verification status')
replace('\\appendix\n\\section{Earlier fixed-graph comparison results}','\\appendix\nThe bounds in the following historical appendices retain their original\nmodels and premises. They are successive earlier results, numerically\nsuperseded by the maintained interval in Theorem~\\ref{thm:main}.\n\n\\section{Earlier fixed-graph comparison results}','Historical appendix scope')
replace(r'\end{thebibliography}',(H/'scripts/new_bibliography.txt').read_text(encoding='utf-8')+r'\end{thebibliography}','New references')
newlabels=['sec:forest220','eq:forest220','eq:forest-cut220','sec:product220','eq:cut-parity220']
assert re.findall(r'\\label\{([^}]+)\}',old)==[x for x in re.findall(r'\\label\{([^}]+)\}',s) if x not in newlabels]
assert re.search(r'\\author\{[^\n]*',old).group()==re.search(r'\\author\{[^\n]*',s).group()
assert re.search(r'\\hypersetup\{.*?\n\}',old,re.S).group()==re.search(r'\\hypersetup\{.*?\n\}',s,re.S).group()
p.write_text(s,encoding='utf-8',newline='\n');(R/'paper/snake9_research.tex').write_bytes(p.read_bytes())
(H/'data/main-edit-record.json').write_text(json.dumps({'changes':changes,'all_old_labels_preserved_in_order':True,'authors_hypersetup_preserved':True},indent=2)+'\n')
print('REVISED_MAIN',len(changes),'changes')
