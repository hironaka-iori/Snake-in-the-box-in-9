"""Save the review outcome and the exact research stopping point."""
from pathlib import Path
from datetime import datetime, timezone
import hashlib
import json
import re
import subprocess

HERE = Path(__file__).resolve().parents[1]
ROOT = HERE.parents[1]
EDITOR = Path('D:/Codex/2026-10-13/new-chat/outputs')
def write(path, text):
    path.write_text(text.strip()+'\n', encoding='utf-8', newline='\n')
def js(path, obj):
    write(path, json.dumps(obj, indent=2, ensure_ascii=False))
def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()
def git(*args):
    return subprocess.check_output(['git','-c','core.commitGraph=false','-c','maintenance.auto=false','-c','gc.auto=0',*args],cwd=ROOT,text=True).strip()

now = datetime.now(timezone.utc).isoformat()
previous = json.loads((ROOT/'milestones/209-slice-capacity/data/completion.json').read_text())
identities = {}
for name, before in [('snake9_research.tex','research-before.tex'),('snake9_frontier_explanation.tex','frontier-before.tex')]:
    original = EDITOR/name
    mirror = ROOT/'paper'/name
    if original.read_bytes()!=mirror.read_bytes():
        raise RuntimeError('Editor and repository document differ: '+name)
    identities[name] = {'editor_source':str(original),'repository_source':str(mirror),
        'sha256':sha(original),'bytes':original.stat().st_size,
        'lines':len(original.read_text(encoding='utf-8').splitlines()),
        'before_sha256':sha(HERE/'data'/before)}
old=(HERE/'data/research-before.tex').read_text(encoding='utf-8')
new=(ROOT/'paper/snake9_research.tex').read_text(encoding='utf-8')
for pattern in [r'\\author\{[^\n]*',r'\\hypersetup\{.*?\n\}']:
    if re.search(pattern,old,re.S).group()!=re.search(pattern,new,re.S).group():
        raise RuntimeError('Author or hypersetup preservation failed')
js(HERE/'data/document-identities.json',identities)

js(HERE/'data/source-refresh.json',{
 'utc':now,'scope':'Primary-source refresh for presentation and status; not an exhaustive literature survey.',
 'sources':[
  {'url':'https://oeis.org/A099155','inspected':'Complete displayed sequence page','supports':'Exact values through dimension eight; a(8)=98 with the cited exhaustive-search reference.'},
  {'url':'https://arxiv.org/html/2607.15270v3','inspected':'Title, author and abstract/front-matter passages','supports':'Published 191-edge Q9 construction; exact optimum reported known only through dimension eight.'},
  {'url':'https://github.com/Math-AI-Caltech/Snake-in-the-Box','inspected':'Public repository README and file listing','supports':'Public construction data and repository scope.'},
  {'url':'https://doi.org/10.1007/s00373-014-1423-3','inspected':'Publisher access unsuccessful','supports':None,'limitation':'No claim to have reviewed publisher full text in round210.'}],
 'contributor_ref':git('rev-parse','origin/research/unconditional-241'),
 'contributor_report':'10:57 UTC 14 November: 3124 of 3127 modules built; not independently rebuilt or merged.',
 'remaining_contributor_modules':['S012301A35344','T012304A33356K63','T012304A35346K47']})

note=r'''
# Round 210: the current argument and its limits

This round reviews the complete manuscript and rewrites its presentation. It proves no new numerical bound, runs no search, and adds no Lean module. All 10,200 original main-paper lines were covered by three bounded reviews, with repaired rereads where an output had been truncated. The entire former short explanation and the rewritten explanation were also read. The exact before snapshots, review reports, revision scripts, compilation receipts and final source hashes are preserved here.

## The argument retained

For a nontrivial Q9 snake with m edges, counting coordinate squares gives

\[
T+2s_0+35(m+1)=9214.
\]

The archived count-only potential and the improved six-count boundary imply

\[
39m+2s_0\le9192.
\]

Thus a length-235 snake would have at most thirteen empty squares. A universal fourteen-empty-square result at that length would imply 234; that premise remains open. The completed archived 235 theorem has a saved successful compilation and axiom audit at revision b20346ee15a43b96de34128bc66b05551244cf31. Its complete independent rebuild remains pending. This reproduction status does not turn the completed archived theorem into an unproved numerical conjecture.

The exact share identity retains the loss L. The already established seven-count boundary and fivefold overlap give

\[
W+4200m+5L\le1098600.
\]

The main actual-edge theorem now states this strongest available total. It uses the same local-share premises as before. The previous boundary-21 comparisons remain valid with their archived constants. Under the current retained profile (15,14,14,14), the graph calculation and remaining universal premises would imply

\[
42254m+45L\le9928453,
\]

hence 234. The separate contributor comparison would imply 233 under its own premises. No local-certificate count or isolated successful module build discharges every condition of either argument.

## Construction deductions retained

Joining across faces is controlled by projected intersections. The general two-parent identity

\[
m+k+b+e+H=p+q+2+2A
\]

counts original within-face parent edges and all final crossings. It sharply limits deletion-only 196-edge constructions, without producing one. The saved 98-edge Q8 parent cannot itself arise by deletion from two Q7 parents: all but one coordinate cut have too many crossings, while the remaining cut has a face of 52 vertices, exceeding the 51 available in one Q7 parent.

Whole-snake slice maps must preserve every selected edge and nonedge. Arbitrary slice isometries give an exact adjacent-slice criterion; literal coverage of the saved finite models is Lean-checked, while the complete geometric table interpretation and leaf-witness replay remain pending. The unrestricted four- and five-history exclusions retain native status. They imply at least six changed histories only for a different class at the same length and fixed index matching to the saved source.

With two retained coordinates, equal free words of one parity can occur in different maximal intervals only at opposite singleton corners. Therefore

\[
M+\max(N_{00},N_{11})+\max(N_{01},N_{10})\le2^{r-1}.
\]

The pair (0,5) saturates this capacity: 32 selected intervals use all 32 even words, and nine outside singleton intervals share words with opposite-corner partners. This provides necessary constraints across the whole ordered path. It neither fixes the partners nor handles every opposite-parity constraint. The three round-209 Lean modules check its geometric core, counting consequences and literal source counts separately; complete model assembly and search certification remain pending.

## Editorial and logical changes

- The main paper now has separate parts for upper-bound deductions and constructions/whole-snake restrictions. Numerical conjectures and the current history/capacity argument precede the final verification section.
- The abstract is shorter. The short explanation is rebuilt around seven consecutive stages of the argument, with brief reasons for each principal deduction.
- The current retained graph and the older accepted-key package are identified separately. Historical profiles retain their original constants and certificate cutoffs.
- The completed stronger domination deduction supersedes the earlier partial-implementation wording. Local share bounds use a different symbol from global loss where they previously collided.
- The missing round-201 citation is supplied. Authors and the existing main-paper hypersetup block are preserved exactly.
- The short explanation states the length, endpoint, original-edge, injectivity, parity and nonadjacency assumptions needed by its condensed proofs.
- All 322 main-paper labels are preserved, and source references/citations resolve. Both current documents compile successfully in the desktop editor. A complete page-by-page rendered-layout audit was not performed.

No software tests were created or run. No claim is made to have independently rebuilt every archived proof or rerun any native exclusion in this review.

## Next mathematical step after an explicit resume

Strengthen the saturated 32-interval assignment with subset capacity. Any k variables whose assigned words must be distinct need at least k words in their combined domains. If their union contains exactly k words, those words are reserved for those variables and can be removed from the other variables in the same distinctness family. The proof is the finite injection/counting argument; this is a standard matching constraint, not a novelty claim.

This is stronger than checking each word separately. A checked generic subset lemma and a sound implementation could reduce the open (0,5) search. Any changed search engine must have an explicit transfer from the saved covering frontier; its states must not silently replace the frozen round-209 evidence. No speed improvement can be predicted without a comparable run.

An exhausted (0,5) model would exclude one more source-specific family. If all 27 remaining cases exhaust, the restriction rises to seven changed histories. A new source-inequivalent parent would be a construction lead requiring a separate compatible Q9 join. Neither outcome alone determines a(9).

The user requested a pause after this round. Publication and the goal pause close this round; no next research round is started.
'''
write(HERE/'MATHEMATICAL_NOTE.md',note)

handoff=r'''
# Stopping point after round 210

The user explicitly requested a pause after this round. Research is stopped at round 210; pause the goal after publication, and resume only on a subsequent user instruction. Round 210 is a complete paper review and presentation revision. No new Q9 witness, global bound, search exclusion or Lean module was obtained. The value 196 remains unresolved.

Read milestones/210-paper-review/MATHEMATICAL_NOTE.md, data/completion.json and the review reports. The main argument now separates upper-bound deductions from constructions and whole-snake restrictions. The short frontier explanation has been rewritten with the full logical chain and brief proofs. Both editor originals compile successfully; repository mirrors match their exact bytes. Preserve the three authors and local hypersetup settings.

## Current mathematical status

The verified construction has 191 edges. The completed archived contributor theorem gives 235, with a successful saved assembly/axiom audit at b20346ee15a43b96de34128bc66b05551244cf31. A complete independent rebuild remains pending. The 233 and 234 improvements remain conditional. Do not conflate the retained 4,661,572-transition graph with the older 4,947,008-key package or transfer one catalogue's progress to another.

For the saved 98-edge Q8 parent, all 70 four-free-coordinate and all 56 five-free-coordinate models exhaust natively. A different cube-isometry class therefore requires at least six changed histories at the same length and fixed index matching. Only retained pair [1,4] is excluded among the 28 six-free-coordinate models; 27 remain unresolved. The other 24 unresolved pairs retain only their initial limited runs.

Round 209 remains the exact search checkpoint:

| Case | Retained coordinates | Committed jobs | Pending regions | Nodes | Status |
|---|---|---:|---:|---:|---|
| 24 | [0,4] | 150 | 8 | 9,625,900 | OPEN |
| 9 | [3,4] | 150 | 3 | 8,142,891 | OPEN |
| 23 | [0,5] | 100 | 7 | 2,683,356 | OPEN |

The square-base capacity argument forces nine antipodal singleton word sharings in case 23. Its three accepted Lean modules have thirteen dependency reports; the complete geometry-to-model assembly and native exclusions remain separate. The source/count receipts and search states are unchanged by round 210.

## Recommended continuation, only after resume

Prove and use subset capacity within the saturated 32-interval distinctness family. If k variables have fewer than k allowed words in their union, the branch is impossible; if exactly k, those words are reserved for that subset. This can strengthen singleton support without prescribing partners. It is a necessary matching condition; the opposite-parity constraints remain essential. Do not claim speed improvement without measurement. Alternatively continue the exact frozen search frontiers with their existing engines.

In a new milestone, copy the original engine scripts, binary and input, plus the complete case-24 and case-9 directories from round209. Also copy capacity_continue.py, capacity_solver.c, capacity_solver.exe, square-capacity.json and the complete case-23 directory. Maintain relative paths and exact engine/model pins. Use continue_search.py for cases 24/9 and capacity_continue.py for case23, sequentially. Their roots follow their file locations. Do not regenerate pinned files or mix the two engines' states. A changed engine requires a justified frontier transfer. Preserve round209 and round210 evidence.

All previous native sessions are terminal. No search or Lean worker was started in round210. Keep one heavy worker at a time. Search/Lean startup requires at least 1 GiB free, reserve at least 768 MiB, and private bytes at most 256 MiB. Lean uses 60 seconds with -j1 -s8192. The bounded 55-second startup wait retains these thresholds. No Python -O; assertions remain enabled and PYTHONOPTIMIZE unset. One coordinator owns continuation. A per-job STOP marker does not promise whole-batch cancellation. Process recovery is supported; full power-loss durability is unproved. Do not create or run software tests unless requested.

The contributor branch last inspected is 7f549f144f5dae2ef9f6164757afd3f1e7bdbc25. Its 10:57 UTC report on 14 November records 3,124 / 3,127 modules built. The three remaining names are S012301A35344, T012304A33356K63 and T012304A35346K47. This is contributor-reported progress, unmerged and not independently rebuilt. Named main and contributor refs were fetched in round210; no new contributor commit was found at that cutoff.

The editor originals are D:/Codex/2026-10-13/new-chat/outputs/snake9_research.tex and snake9_frontier_explanation.tex; mirrors are in E:/Snake-in-a-box/paper. Compile frontier first and main last. Current successful receipts are in milestone210/data. Preserve unrelated .gitignore, milestone50 critical-family.json and all pre-existing untracked files; avoid unfiltered git status. Use exact narrowly scoped publication manifests and wait for every commit/push command to finish. The next scheduled whole-paper review is round220, unless earlier changes require one.
'''
write(ROOT/'handoff/CURRENT_STATUS.md',handoff)
write(ROOT/'handoff/NEXT_AGENT_PROMPT.md',handoff)
readme=r'''
# Current result after round 210

The complete paper has been reviewed and reorganized into upper-bound deductions and constructions/whole-snake restrictions. The short frontier explanation now gives the logical chain with brief proofs. Both documents compile successfully; authors and the main paper's local hypersetup settings are preserved.

The research frontier is unchanged: a verified 191-edge construction, the completed archived 235 theorem with its independent rebuild pending, conditional routes to 234 and 233, and 27 unresolved six-history models of the saved Q8 parent. No new mathematical bound, search exclusion or Lean module is claimed in this review. The user requested a pause after this round; resume only on a new instruction.

Read [the review and current argument](milestones/210-paper-review/MATHEMATICAL_NOTE.md), [completion record](milestones/210-paper-review/data/completion.json), [handoff](handoff/CURRENT_STATUS.md), [main paper](paper/snake9_research.tex) and [short frontier explanation](paper/snake9_frontier_explanation.tex). Frozen search states remain in [round209](milestones/209-slice-capacity).

## Earlier checkpoints

'''
existing=(ROOT/'README.md').read_text(encoding='utf-8')
if not existing.startswith('# Current result after round 210'):
    write(ROOT/'README.md',readme.strip()+'\n\n'+existing)

completion={
 'round':210,'status':'REVIEW_COMPLETE','utc':now,
 'started_utc':'2026-11-14T11:11:13+00:00',
 'base_head':git('rev-parse','HEAD'),
 'pause_requested':True,'requested_final_goal_state':'PAUSED',
 'goal_action':'Pause after successful publication; no subsequent research round.',
 'new_q9_record':False,'new_global_bound':False,'new_native_exclusions':0,
 'accepted_lean_modules_this_round':0,'software_tests_created_or_run':False,
 'whole_original_main_paper_reviewed_lines':10200,
 'main_review_ranges':[[1,3300],[3301,6300],[6301,10200]],
 'main_review_reports':['logs/review-main-1.md','logs/review-main-2.md','logs/review-main-3.md'],
 'revision_reviews':['logs/review-revision.md','logs/review-frontier.md'],
 'documents':identities,'compile_receipts':['data/frontier-compile.json','data/main-compile.json'],
 'search_checkpoint':'milestones/209-slice-capacity/data/completion.json',
 'search_checkpoint_sha256':sha(ROOT/'milestones/209-slice-capacity/data/completion.json'),
 'unchanged_search_cases':previous['cases'],
 'six_coordinate_total_exhausted':1,'six_coordinate_total_unresolved':27,
 'next_step_after_resume':'Subset capacity in the saturated 32-interval distinctness family, with a checked generic implication and explicit search-frontier transfer; or exact continuation of frozen searches.',
 'limits':['No clean rebuild of the full archived235 dependency closure.','No rerun or new certification of native exclusions.','No new Lean compilation this round.','No complete page-by-page visual audit.']}
js(HERE/'data/completion.json',completion)
write(HERE/'README.md',r'''
# Round 210: whole-paper review

The full manuscript is reviewed and reorganized; the short explanation is rewritten with the current deduction chain and brief reasons. The mathematical frontier is unchanged. The user requested a pause after this round.

- [Argument, corrections, limitations and next mathematical step](MATHEMATICAL_NOTE.md)
- [Completion record and exact search checkpoint](data/completion.json)
- [Final document identities](data/document-identities.json)
- [Main source reviews](logs/review-main-1.md), [continued](logs/review-main-2.md), [construction and references](logs/review-main-3.md)
- [Revised-main review](logs/review-revision.md) and [short-explanation review](logs/review-frontier.md)
- [Main compilation](data/main-compile.json) and [frontier compilation](data/frontier-compile.json)
- [Primary-source refresh](data/source-refresh.json)

Before snapshots and deterministic revision scripts are retained. No software tests, new proof compilation, or native searches were run. Historical proof and search receipts retain their original scope. Resume only after a new user instruction.
''')
helper=HERE/'scripts/publication.py'
write(helper,helper.read_text(encoding='utf-8').replace('Round209 research artifacts','Round210 review artifacts'))
print(json.dumps({'saved_round':210,'utc':now,'documents':identities,'requested_final_goal_state':'PAUSED'},indent=2))
