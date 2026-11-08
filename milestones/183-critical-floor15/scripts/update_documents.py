from pathlib import Path
import json,re,shutil
H=Path(__file__).resolve().parents[1];R=H.parents[1]
EDITOR=Path('D:/Codex/2026-10-13/new-chat/outputs')
for label in ['012034-floor15','012034-floor15-core','012034-floor15-dense']:
 assert json.loads((H/'data'/(label+'-replay.json')).read_text())['status']=='PASS_FULL_ORDERED_RUP_REPLAY'
paragraph=r'''\paragraph{A smaller certificate for the critical floor fifteen.}
The radius-four query for $012034$ excluding integer share at most fourteen
now has a complete native refutation. It uses the broad count intervals
$[0,21]$ and the existing local constraints, with no additional extension
or cycle clauses. Its complete replay checks 119,146 deductions.
Extracting the dependency closure of the final contradiction reduces this
to 12,424 original clauses and 52,489 deductions, with 3,619,677 propagation
hints. Both this core and its dense variable renaming pass separate full
native replays. The dense proof has 5,342 variables; a last-use schedule
needs at most 12,593 stored clauses. These sizes fit the existing Lean
checker's data format, while the actual kernel replay and geometric
interpretation remain unfinished.

This certificate addresses the shape occurring six times on the critical
nine-edge cycle. It motivates checking the weaker profile $(15,14,14,14)$,
in the order $012034,012301,012340,012345$. Whether that profile already
removes the loss premise requires a fresh full retained-graph calculation.
No improved global comparison is asserted from the local certificate alone.
'''
for name in ['snake9_research.tex','snake9_frontier_explanation.tex']:
 p=EDITOR/name;original=p.read_text(encoding='utf-8');assert original==(R/'paper'/name).read_text(encoding='utf-8')
 backup=H/'source-before'/name;backup.parent.mkdir(exist_ok=True)
 if not backup.exists():shutil.copyfile(p,backup)
 boundary=r'\section{Remaining requirements for a stronger bound}' if name=='snake9_research.tex' else r'\textbf{6. What is proved, and what remains.}'
 assert original.count(boundary)==1
 text=original.replace(boundary,paragraph+'\n'+boundary,1)
 if name=='snake9_frontier_explanation.tex':
  text=text.replace('Research state after round 182','Research state after round 183')
  text=text.replace('Round 182 completes the requested continuation. Research pauses at\nthis frontier; these outstanding requirements remain unresolved.',
                    'Round 183 is the first of two requested rounds. Round 184 will examine\nthe weaker share profile; research will pause after that round.')
  text=text.replace('research records 175--182.','research records 175--183.')
 assert re.findall(r'\\author\{[^\n]*',text)==re.findall(r'\\author\{[^\n]*',original)
 assert re.findall(r'\\hypersetup\{.*?\n\}',text,re.S)==re.findall(r'\\hypersetup\{.*?\n\}',original,re.S)
 p.write_text(text,encoding='utf-8',newline='\n');shutil.copyfile(p,R/'paper'/name)
old=(R/'handoff/CURRENT_STATUS.md').read_text(encoding='utf-8')
(H/'data/prior-status.md').write_text(old,encoding='utf-8')
status='''# Round 183 complete: one of two requested rounds

The current instruction is to complete rounds 183 and 184, then pause. Round 183 is complete; round 184 remains. Do not pause early or begin round 185.

The critical 012034 floor-15 input returned UNSAT and passed full native replay: 119,146 deductions, 4,922,578 hints. Dependency extraction gives 12,424 original clauses and 52,489 deductions, with 3,619,677 hints. Both the extracted core and dense variable renaming passed complete native replay. The dense core uses 5,342 variables and its measured last-use peak is 12,593 stored clauses, fitting the existing offset-8192 and 14-bit-slot checker formats. No Lean replay of this new proof has been run. Clause semantics and the initial-database truth bridge remain necessary.

No new extension or cycle clauses were added for 012034. The core retains the local endpoint counter, degree conditions, squares and six-cycle exclusions. Its tag audit does not remove any of those geometric requirements. The cap transformation reuses the round-182 construction and its checked truncation arithmetic. No new Lean theorem is claimed for this round.

The four floor-14 inputs already have completed native replays. The representative-extension 012301 floor-15 input also has a completed native replay; its full isometry and semantic transfer remain pending. Round182 checked that a 012301 window extends through an unused coordinate when m>=7, and proved the obstruction to raising only that floor: profile (14,15,14,14) cannot make the loss-one comparison smaller than 235+21/42248.

Round184 should now examine (15,14,14,14), then (15,15,14,14) only if useful, in the order 012034,012301,012340,012345. The critical nine-cycle has six 012034 edges and no 012301 edge. Reconstruct weights, scan all retained edge inequalities and check actual-snake conditional arithmetic in Lean before claiming a stronger sufficient profile.

The current comparison is still 42248m+45L<=9928364 under retained premises. It yields conditional234 when L>=2, with remaining m=235 and L in{0,1}. A strict rational-share bound >72/5 remains sufficient for floor15 under L<=1, but is unproved. The maintained interval is191–235 with the archived235 proof's complete independent rebuild pending. No longer construction, proof of196 or new unconditional bound is obtained.

Inherited gaps remain: the hypothetical0123104 six-count floor25 under its exact first-count condition, 1358 reference entries, 791 context obligations, complete graph coverage and Lean local/finite-edge certificates. The older share-18 Lean replay is unchanged at33,111/145,215 deductions. Do not confuse it with the new native certificates.

Read milestones/183-critical-floor15/README.md and data/completion.json. Manuscripts are updated in the original D: editor files and mirrored to E:/Snake-in-a-box/paper, preserving all three authors and hypersetup. Next full paper review remains186. Preserve unrelated .gitignore and milestone50 edits. Exact proof inputs, mappings, failures and receipts remain saved.
'''
(R/'handoff/CURRENT_STATUS.md').write_text(status,encoding='utf-8')
(R/'handoff/NEXT_AGENT_PROMPT.md').write_text('''# Continue with round184, then pause

One of the user's two requested rounds is complete. Read CURRENT_STATUS.md and milestones/183-critical-floor15/README.md. Do not start round185.

The new local evidence supports examining profile(15,14,14,14). Use the existing bounded streamed potential producer, reconstruct its weights from the exact original rows and keep the retained graph mask and unresolved count assumptions explicit. Scan every edge of an accepted potential; check the actual-snake conditional implication in Lean. Compare the two-floor upgrade only if the single upgrade fails or reveals a material difference.

The 012034 floor15 certificate, its dependency core and dense renaming all pass native replay. The dense input has5342 variables,12424 original clauses,52489 deductions and3619677 hints. A measured last-use schedule peaks at12593 clauses. These fit the existing checker format; no new kernel replay or initial truth bridge is complete. Avoid starting another unconnected partial replay merely because the data fit. Preserve the original mappings and all hashes.

The full mathematical objective remains unresolved. Current global range191–235 carries the archived235 independent-rebuild qualification. Do not conceal the hypothetical0123104 floor25, reference/context exclusions or graph-to-snake/Lean gaps. Preserve author order, hypersetup, original editor files and E: mirrors. Publish round184, update the frontier explanation, call the goal pause operation and stop.
''',encoding='utf-8')
p=R/'README.md';old=p.read_text(encoding='utf-8');cut=old.index('## Earlier checkpoints')
p.write_text('''# Current result after round183

The first of two requested rounds is complete. The critical012034 floor15 input now has a complete native refutation, reduced to a replayed dependency core of52489 deductions and5342 variables. Its full Lean and geometric interpretation remain unfinished.

Round184 will examine whether profile(15,14,14,14) already removes the loss premise from the retained comparison, then research will pause. No new unconditional bound is claimed; the maintained range191–235 retains the archived235 independent-rebuild qualification.

Read [round183](milestones/183-critical-floor15/README.md), [the current handoff](handoff/CURRENT_STATUS.md) and [the short explanation](paper/snake9_frontier_explanation.tex).

'''+old[cut:],encoding='utf-8')
(H/'data/completion.json').write_text(json.dumps({'round':183,'status':'COMPLETE_CRITICAL_NATIVE_CERTIFICATE_AND_KERNEL_INPUT_PREPARATION','requested_rounds_completed':1,'requested_rounds_remaining':1,'pause_after':184,'native_floor15_refutation':True,'core_refutation_replayed':True,'dense_refutation_replayed':True,'Lean_refutation_complete':False,'new_unconditional_bound':False},indent=2)+'\n')
print('Updated round183 manuscripts and handoff; one round remains.')
