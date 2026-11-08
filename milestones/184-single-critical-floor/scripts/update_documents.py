"""Put the weaker sufficient profile first and preserve previous evidence."""
from pathlib import Path
import json,re,shutil
H=Path(__file__).resolve().parents[1];R=H.parents[1]
EDITOR=Path('D:/Codex/2026-10-13/new-chat/outputs')
result=json.loads((H/'data/critical15-refined.json').read_text())
assert result['status']=='PASS_POTENTIAL' and result['scan']=={'edges':4661572,'minimum_slack':0,'violations':0}
assert result['scaled_mean']==4454 and result['scaled_range']==5421
core=json.loads((H/'data/SingleCritical184-audit.json').read_text());assert core['status']=='PASS'
actual_path=H/'data/ActualSingleCritical184-audit.json'
actual=actual_path.exists() and json.loads(actual_path.read_text())['status']=='PASS'
lean_status=('Lean also checks the implication for actual snakes, with the local-window\n'
             'and potential inequalities retained as explicit premises.' if actual else
             'The arithmetic passed Lean. Its separate actual-snake wrapper remains\n'
             'pending; the written deduction uses the previously checked physical budget and packing.')
argument=r'''\paragraph{One critical floor fifteen suffices.}
The weaker pending-share profile
\[
(15,14,14,14),\qquad\text{for }012034,012301,012340,012345,
\]
admits a retained-graph potential with $\mu=4454/9$ and $R=5421/9$.
All 4,661,572 edge inequalities passed an exact integer scan, after
reconstruction reproduced three archived weight hashes. Substituting
in the boundary-24 comparison gives
\[
\boxed{42254m+45L\le9928453.}
\]
Since $L\ge0$ and $235\cdot42254=9928453+1237$, this yields
\[
m\le235-\frac{1237}{42254}<235,\qquad m\le234.
\]
Thus only the critical pending floor must reach fifteen; the other three
may remain fourteen. No separate exclusion of $L=0$ or $L=1$ is required
for this sufficient profile. LEAN_STATUS

A reconstructed nine-edge cycle has weight 4454, and a 24-edge walk has
weight 11275. Hence every admissible mean and range for this fixed graph
satisfies $9\mu\le4454$ and $R\ge24\mu-11275$. Consequently,
\[
\frac{1098600+8\mu+R}{4200+\mu}
\ge\frac{1087325+32\mu}{4200+\mu}
\ge\frac{9928453}{42254}.
\]
The middle expression decreases with $\mu$, and the new potential attains
the final value at $\mu=4454/9$. The denominator-cleared optimality
deduction passes Lean. This proves optimality of the loss-free comparison
for the fixed profile, boundary and zero occurrence credit.

Fifteen is also the least sufficient integer floor for $012034$ when the
other pending floors stay fourteen in this argument. At uniform floor
fourteen, the saved cycle and walk force $9\mu\le4448$ and
$R\ge8\mu-3356$, keeping the loss-zero comparison strictly above 235.
The strict arithmetic obstruction passes Lean; lowering that floor further
only weakens edge weights.

Every numerical floor in the new profile has a complete native Boolean
refutation. The $012301$ floor-fourteen input uses the necessary extension
condition for snakes with at least seven edges; shorter snakes already
satisfy the desired global bound. The full Lean contradiction chains,
geometric interpretation and inherited count and graph premises remain
unfinished. The optimized comparison therefore remains conditional.
'''.replace('LEAN_STATUS',lean_status)

for name in ['snake9_research.tex','snake9_frontier_explanation.tex']:
 p=EDITOR/name;original=p.read_text(encoding='utf-8');assert original==(R/'paper'/name).read_text(encoding='utf-8')
 backup=H/'source-before'/name;backup.parent.mkdir(exist_ok=True)
 if not backup.exists():shutil.copyfile(p,backup)
 text=original
 if name=='snake9_research.tex':
  boundary=r'\section{Remaining requirements for a stronger bound}'
  assert text.count(boundary)==1;text=text.replace(boundary,argument+'\n'+boundary,1)
  old=('lowers all four pending floors simultaneously to fifteen. Uniform floor\n'
       'fourteen also suffices when total rounding loss is at least two.\n'
       'The remaining hypothetical 235-edge case has loss zero or one.')
  new=('lowers all four pending floors simultaneously to fifteen. Further\n'
       'optimization shows that only the $012034$ floor must reach fifteen;\n'
       'the other three pending floors may stay fourteen. The resulting\n'
       'conditional comparison is $m\\le235-1237/42254<235$, with no\n'
       'positive-loss premise. A cycle and a 24-edge walk prove that this\n'
       'comparison is optimal for the fixed profile and accounting.')
  assert old in text;text=text.replace(old,new,1)
 else:
  text=text.replace('Research state after round 183','Research state after round 184')
  start=text.index('proof. The current conditional result is:')
  end=text.index(r'\textbf{1. The exact square budget.}',start)
  text=text[:start]+r'''proof. The current sufficient pending-share profile is $(15,14,14,14)$
for $012034,012301,012340,012345$, respectively. Together with the retained
local and graph premises, it implies $m\le234$ without a positive-loss
assumption. All four required numerical floors have native contradiction
certificates; their complete Lean and geometric interpretation, and the
inherited graph requirements, remain unfinished. The argument and these
limitations are given in order.

'''+text[end:]
  start=text.index(r'\textbf{4. The conditional route with no positive-loss premise.}')
  end=text.index(r'\textbf{5. Floor fourteen and the two remaining loss cases.}',start)
  section4=r'''\textbf{4. One critical floor fifteen gives the conditional bound.}
A direction pattern records successive coordinate flips, with labels renamed
consistently. A share floor bounds the sum at the associated five window
centres. The finite retained graph has 4,661,572 edges. The current sufficient
floors, ordered as $012034,012301,012340,012345$, are $(15,14,14,14)$.
The graph construction retains all its previously stated count and exclusion
premises.

'''+argument.replace(r'\paragraph{One critical floor fifteen suffices.}'+'\n','',1)+r'''
An earlier sufficient profile raised all four pending floors to fifteen.
The new profile weakens three of those requirements. Its purpose is to
reduce the local proof obligations while retaining the conditional bound 234.

'''
  text=text[:start]+section4+text[end:]
  text=text.replace(r'\textbf{5. Floor fourteen and the two remaining loss cases.}',
                    r'\textbf{5. An alternative route using only floor fourteen.}')
  text=text.replace('New potentials improve the earlier sufficient loss thresholds. Under\n'
                    'the same retained graph and count premises, they give',
                    'If the critical floor is left at fourteen, the following earlier\n'
                    'comparisons still apply under their retained graph and count premises:')
  text=text.replace('Whether that profile already\nremoves the loss premise requires a fresh full retained-graph calculation.\nNo improved global comparison is asserted from the local certificate alone.',
                    'The full retained-graph calculation in Section 4 now establishes its\nsufficiency under the stated premises. The local certificate alone\ndoes not establish the global comparison.')
  # Replace the current requirements rather than leaving low-loss exclusion mandatory.
  start=text.index('The remaining work is therefore:')
  end=text.index(r'\smallskip',start)
  text=text[:start]+r'''The remaining work is therefore:
\begin{enumerate}
\item Complete the Lean contradiction and geometric interpretation for
the required profile $(15,14,14,14)$. The compact critical certificate
contains 52,489 deductions and 5,342 variables.
\item Discharge the retained count restrictions, reference and context
exclusions, graph coverage and complete finite-edge certificate. These
remain essential assumptions of the conditional upper bound.
\item If an alternative argument is pursued, the uniform floor-fourteen
route still needs to remove its loss-zero and loss-one cases. The separate
count-only route would be completed by proving $s_0\ge14$ for a hypothetical
235-edge snake. Neither alternative is required by the new sufficient
profile once its own premises are proved.
\end{enumerate}
Rounds 183 and 184 complete the two requested rounds. Research pauses
at this frontier. No unconditional numerical bound or longer construction
has been added.

'''+text[end:]
  text=text.replace('research records 175--183.','research records 175--184.')
 text=text.replace('It motivates checking the weaker profile', 'It supplies the critical local input for the weaker profile')
 text=text.replace('Whether that profile already\nremoves the loss premise requires a fresh full retained-graph calculation.\nNo improved global comparison is asserted from the local certificate alone.', 'The full retained-graph calculation below confirms its sufficiency\nunder the stated premises. The local certificate alone does not\nestablish the global comparison.')
 assert re.findall(r'\\author\{[^\n]*',text)==re.findall(r'\\author\{[^\n]*',original)
 assert re.findall(r'\\hypersetup\{.*?\n\}',text,re.S)==re.findall(r'\\hypersetup\{.*?\n\}',original,re.S)
 p.write_text(text,encoding='utf-8',newline='\n');shutil.copyfile(p,R/'paper'/name)

status=f'''# Round184 complete: both requested rounds finished; pause

Rounds183 and184 complete the user's two-round instruction. Pause the goal after publication. Do not start round185 without a new instruction to resume.

The new sufficient pending-share profile is (15,14,14,14), in the order012034,012301,012340,012345. Its refined potential has mean4454/9 and range5421/9. All4,661,572 retained edge inequalities passed exact integer scans after reconstruction reproduced three archived weight hashes. The resulting conditional inequality is42254m+45L<=9928453, so m<=235-1237/42254<235 and hence m<=234 using only L>=0. The previous requirement that all four pending floors reach15 is unnecessary for this profile. The remaining loss-zero and loss-one cases do not need separate exclusion on this route.

A nine-edge cycle of weight4454 and a24-edge walk of weight11275 force9mu<=4454 and R>=24mu-11275. Independent scalar source-row reconstruction checks both witnesses. Lean checks optimality of the displayed loss-free mean/range comparison for this fixed profile, boundary and zero occurrence credit. Fifteen is the least sufficient integer critical floor when the other three stay14 in this argument; the uniform14 cycle/walk obstruction remains strictly above235 at L=0. No broader optimality claim is made.

The arithmetic module passed five Lean dependency reports. The separate actual-snake wrapper accepted status is {actual}; it retains explicit truncation, physical-share, local-window and potential premises. Consult its receipt before describing that application as checked. Full Lean edge certification and universal geometric coverage remain unfinished.

Round183 supplies a complete native 012034 floor15 proof and a separately replayed dependency core:12,424 original clauses,52,489 deductions,3,619,677 hints and5,342 densely renamed variables. A measured last-use schedule peaks at12,593 clauses, fitting the existing checker format. The kernel replay and initial-database truth bridge are incomplete. The other three required floor14 inputs have complete native replays. The012301 input includes the necessary extension condition for m>=7; shorter snakes trivially satisfy234.

The original mean4453/9, range5402/9 potential remains saved. An initial scalar script incorrectly expected the archived cycle to weigh4453. Reconstruction rejected it; the corrected weight4454 motivated the successful refined potential. The failed source and correction record are preserved. The final comparison uses only accepted evidence.

The project interval remains191–235, with the archived235 proof's complete independent rebuild pending. The numerical upper234 is still conditional. Inherited gaps include hypothetical0123104 six-count floor25 with its exact first-count condition,1358 reference entries,791 context obligations, graph-to-snake coverage and complete Lean local/finite-edge certificates. The older share18 Lean replay stays at33,111/145,215 deductions. No longer construction or proof of196 was obtained.

The main manuscript and short explanation are updated in the original D: editor files and E:/Snake-in-a-box/paper mirrors, with author order and hypersetup preserved. Read milestones/184-single-critical-floor/README.md and data/completion.json. Next full manuscript review remains186. Preserve unrelated .gitignore and milestone50 changes. No heavy worker should remain after publication.
'''
(R/'handoff/CURRENT_STATUS.md').write_text(status,encoding='utf-8')
(R/'handoff/NEXT_AGENT_PROMPT.md').write_text(f'''# Paused after rounds183–184

Resume only on a new user instruction. Do not start round185 automatically. Read CURRENT_STATUS.md and milestones/184-single-critical-floor/README.md.

The selected route now needs only profile(15,14,14,14). Mean4454/9 and range5421/9 give42254m+45L<=9928453 and conditional234 with no positive-loss premise. Exact scans cover all retained edges. A nine-cycle4454 and24-edge walk11275 prove optimality of this fixed mean/range comparison. Retuning the same profile cannot improve it. The actual-snake wrapper's accepted Lean status is {actual}; inspect data/ActualSingleCritical184-audit.json before citing it.

Prioritize closing the existing proof chain. The critical012034 floor15 certificate from round183 has a fully replayed dense core with5342 variables,12424 initial clauses,52489 deductions and3619677 hints. Its measured live-clause peak12593 fits the older checker's offset8192 and14-bit slots. This format fit is not a completed Lean proof. Preserve original-clause mappings, variable maps and input hashes. Complete the initial-database truth and geometric interpretation together with the refutation, rather than beginning an unrelated partial replay.

The other three floor14 inputs already have native certificates. The012301 input uses the necessary extension property for m>=7. The stronger fixed-extension floor15 certificate from182 is available but is unnecessary for the current sufficient profile. The low-loss L=0/1 branch is an alternative route, not an additional requirement of the new comparison.

Do not hide the remaining hypothetical0123104 count condition, reference/context exclusions, graph coverage or full finite-edge Lean obligations. No unconditional234 or optimum claim is justified yet. Check GitHub before new research. Keep core Lean startup1GiB/private256MiB/reserve768MiB and Mathlib startup2GiB/private3GiB/reserve768MiB guards. The streamed graph producer uses startup1.25GiB/private512MiB with the same reserve. Confirm prior jobs are terminal before restarting; preserve failed attempts. Preserve authors, hypersetup, original editor files, E: mirrors and unrelated changes. No software tests are authorized; mathematical Lean verification is authorized.
''',encoding='utf-8')
p=R/'README.md';old=p.read_text(encoding='utf-8');cut=old.index('## Earlier checkpoints')
p.write_text('''# Current result after round184

The two requested rounds,183 and184, are complete; research pauses here. The weaker pending-share profile(15,14,14,14) suffices for conditional234 without positive loss. Its refined potential gives42254m+45L<=9928453, and a cycle/walk argument proves the comparison optimal for the fixed profile and accounting.

All numerical local floors in this profile have native contradiction certificates. Their full Lean and geometric interpretation, and the inherited graph/count requirements, remain unfinished. The maintained project range is191–235, with the archived235 independent-rebuild qualification. No new unconditional numerical bound is claimed.

Read [round184](milestones/184-single-critical-floor/README.md), [the current handoff](handoff/CURRENT_STATUS.md), [the main manuscript](paper/snake9_research.tex) and [the frontier explanation](paper/snake9_frontier_explanation.tex).

'''+old[cut:],encoding='utf-8')
completion={'round':184,'status':'COMPLETE_SINGLE_CRITICAL_FLOOR_PROFILE','requested_rounds_completed':2,'requested_rounds_remaining':0,'pause_requested':True,'next_round_started':False,'pending_share_profile':[15,14,14,14],'scaled_mean':4454,'scale':9,'scaled_range':5421,'retained_edges_checked':4661572,'comparison':'42254*m+45*L<=9928453','positive_loss_required':False,'conditional_upper':234,'fixed_profile_comparison_optimal':True,'core_Lean_dependency_reports':5,'actual_snake_wrapper_Lean_checked':actual,'new_unconditional_bound':False,'complete_local_Lean_certificates':False,'complete_graph_to_snake_certificate':False}
(H/'data/completion.json').write_text(json.dumps(completion,indent=2)+'\n')
print('Updated round184 frontier and handoff; both rounds complete; actual-snake Lean status:',actual)
