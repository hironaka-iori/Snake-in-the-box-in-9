from pathlib import Path
import json,hashlib,re,datetime
R=Path('E:/Snake-in-a-box');H=R/'milestones/190-exchange-constraints';P=R/'milestones/189-middle-replacements';D=Path('D:/Codex/2026-10-13/new-chat');O=D/'outputs';W=D/'work'
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
nearest=json.loads((H/'data/nearest-replacement.json').read_text());classification=json.loads((H/'data/nearest-classification.json').read_text());assert nearest['actual_path'] and classification['same_ordered_path_as_hint']
nearest_text=r'''A 120-second overlap-maximization run returns the supplied known
97-edge seed, retaining 52 of the original 96 vertices. No closer path
was found, and optimality was not established. The seed has 30 forbidden
overlaps in the first surrounding configuration, so it does not yield
a nine-dimensional improvement. Across all endpoint-preserving placements
of this displayed seed family, 52 is the largest retained intersection.
Thus the current lower restriction of six omitted vertices and the
explicit example omitting 44 leave a substantial gap for the minimum
number of omissions. The lower restriction retains the computational
verification qualifications above. A larger contiguous replacement,
separated changes, and revised crossing vertices remain possible.
'''
main=O/'snake9_research.tex';short=O/'snake9_frontier_explanation.tex';a=main.read_text(encoding='utf-8');b=short.read_text(encoding='utf-8');original=a
section=(W/'round190_section.tex').read_text().replace('% ROUND190_NEAREST_RESULT',nearest_text+'\nThe saved equations, search models, outcomes and proof receipts are\nrecorded in~\\cite{exchange190archive}.\n')
brief=(W/'round190_short.tex').read_text().replace('% ROUND190_NEAREST_RESULT',nearest_text)
marker='\\section{Construction experiments and their scope}\\label{app:experiments}'
assert a.count(marker)==1 and 'sec:exchange-balance' not in a;a=a.replace(marker,section+'\n'+marker)
a=a.replace('Fixed-component searches and replacement enumerations identify\nrestrictions in this family without producing a longer snake.','Fixed-component searches and replacement enumerations identify\nrestrictions in this family without producing a longer snake. An exact\nedge count shows that fixed-endpoint replacements preserve the number\nof components among the deleted and added vertices; the current\ncomputational exclusions require at least six omitted vertices to\nreplace the common 95-edge path by a 97-edge path.')
b=b.replace('Research state after round 189','Research state after round 190').replace('\\textbf{7. What is proved, and what remains.}',brief+'\n\\textbf{7. What is proved, and what remains.}')
b=b.replace('Round 189 adds replacement restrictions within the common construction\nfamily and a checked overlap-repair inequality.','Round 190 adds the replacement component balance and the five-omission\nexclusion. The manuscript-wide consistency review is complete; it does\nnot replace the pending certificate and proof rebuilds.').replace('research records 175--189','research records 175--190')
bib=r'''
\bibitem{exchange190archive}
I.~Hironaka, T.~Ma, and S.~Zhan. \emph{Component balance and five-omission replacement restrictions}. Research record 190, 11 November 2026. Finite edge-accounting proofs, complete two-interval enumeration, degree-and-square relaxation, nearest-seed search and manuscript-review receipt:
\url{https://github.com/hironaka-iori/Snake-in-the-box-in-9/tree/main/milestones/190-exchange-constraints}.
'''
a=a.replace('\\end{thebibliography}',bib+'\n\\end{thebibliography}')
for pattern in [r'\\author\{[^\n]+',r'\\hypersetup\{.*?\n\}']:assert re.search(pattern,a,re.S).group()==re.search(pattern,original,re.S).group()
main.write_text(a,encoding='utf-8',newline='\n');short.write_text(b,encoding='utf-8',newline='\n')
for n in [main.name,short.name]:(R/'paper'/n).write_bytes((O/n).read_bytes())
order=json.loads((H/'data/current-order.json').read_text());accepted=[];pins={}
for n in order:
    p=H/'data'/(n+'-audit.json');rec=json.loads(p.read_text());assert rec['status']=='PASS' and rec['exit_code']==0 and rec['stop_reason'] is None
    assert sha(rec['source'])==rec['source_sha256'] and sha(rec['object'])==rec['olean_sha256'] and sha(rec['log'])==rec['log_sha256']
    for q,h in rec['dependencies'].items():
        if q in pins:assert pins[q]==h
        pins[q]=h
    accepted.append({'module':n,'receipt_sha256':sha(p),'reports':len(rec['axioms'])})
for q,h in pins.items():assert sha(q)==h,q
failed=[]
for p in (H/'logs').glob('*/record.json'):
    r=json.loads(p.read_text())
    if r['status']!='PASS':failed.append({'record':str(p.relative_to(H)),'status':r['status'],'reason':r.get('stop_reason')})
completion={'round':190,'status':'PROGRESS','previous_turn':'PROGRESS: round189 published replacement restrictions and checked overlap repair.','utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'goal_status':'pause_after_publication_requested_by_user','accepted_modules':accepted,'failed_attempts':failed,'mathematical_result':'For fixed-endpoint induced path replacements with gain delta, e(A)=e(D)+delta and deleted/added induced forests have equal component counts. Finite edge identities and arithmetic checked under explicit degree/size premises; arbitrary-path bridge remains written.','native_five_omission_coverage':{'one_interval':'Round189 contiguous-size5 completed.','two_intervals':'16020 pairs; both orientations of retained middle chain; no replacement.','three_or_more_intervals':'Degree/square relaxation INFEASIBLE;1792 square cuts; zero dynamic cycle cuts.'},'minimum_omissions_for_fixed_port97':{'value':6,'status':'computational; complete Lean contradiction certificate pending'},'nearest_search':{'status':nearest['status'],'retained_old_vertices':52,'omissions':44,'same_as_known_seed':True,'first_context_forbidden_overlap':30,'optimality':False},'new_q9_record':False,'new_global_upper_bound':False,'manuscript_review':'Completed whole-source consistency/domain/evidence-status review; no full proof rebuild claimed.','next_scheduled_review':200,'resume_task':'Investigate six-omission replacements or larger contiguous/multi-component changes using component balance; check any resulting97-edge witness against all84surrounding contexts. Preserve all existing proofs and qualified upper-bound work.','contributor_head':'f393c48e5e583e57d3cbb66e4330f960033229b1'}
(H/'data/completion.json').write_text(json.dumps(completion,indent=2)+'\n')
note='''# Round 190: component balance and five-omission restrictions

The user requested a pause after this round. Complete publication, then pause the goal. Do not start round 191 without a new resume instruction.

## General mathematical result

Let P,Q be induced paths in the same graph with the same endpoints, with Q longer by delta edges. Let D=V(P)\\V(Q), A=V(Q)\\V(P), C=V(P)∩V(Q), and r=|D|. Then |A|=r+delta. All vertices of D and A are internal in their respective paths, hence2r=2e(D)+e(D,C) and2(r+delta)=2e(A)+e(A,C). Their common induced edges are identical. Subtracting the total edge counts and using these degree sums gives

e(A)=e(D)+delta,
e(A,C)=e(D,C)=2(r−e(D)).

Both D and A induce path forests. Their component counts are r−e(D) and(r+delta)−e(A), so they are equal. This applies to arbitrary induced paths with fixed endpoints; the induced and endpoint hypotheses are essential. No novelty claim is made.

Lean checks the per-edge identities, their summation, and the conclusions under explicit degree and size premises. The full conversion of arbitrary induced paths to the finite-list premises remains a written argument. Four modules have accepted receipts with seven dependency reports. Three large-module attempts hit the unchanged256MiB limit; the final split modules pass and all failed source snapshots remain saved.

## Five-omission classification and computations

For r=5 and delta=2, the seven added vertices have e(D)+2 internal edges. If the five deleted vertices form c intervals, e(D)=5−c. Thus c=1,2,3,4,5 gives e(A)=6,5,4,3,2 respectively.

The general circuit search with five omissions is UNKNOWN after120seconds. The two-interval circuit subcase is UNKNOWN after60seconds. These outcomes do not exclude anything by themselves.

The two-interval case was then independently enumerated. The four ordered splits(1,4),(2,3),(3,2),(4,1) have4005 placements each, for16020 in total. Their deletion leaves three retained chains. Both orientations of the middle chain and all connector-length pairs2..7 summing to9 were considered. All cases completed;59750 admissible length cases produced only6 candidate connector pairs, all invalid together. No replacement exists in this native enumeration. It permits any outsideQ8vertices, withoutQ9outer restrictions. The one-interval case is already covered by round189's contiguous-size5 enumeration.

For c≥3, a smaller degree model selects98vertices, retains91old vertices, fixes the two ports, requires degree1 at ports and degree2 at other selected vertices, and imposes the exact edge identity and e(D)≤2. All1792 coordinate squares have at most3selected vertices. These conditions are necessary for every desired induced path. The model is a relaxation because longer disconnected cycles are still allowed. It reports INFEASIBLE in3.062seconds before any dynamic cycle cut is added. Hence this relaxation excludes all remaining five-omission paths.

Combining these computations with round189 excludes up to five omissions, so a97-edge path between the common95-edge path's ports must omit at least6original vertices and add at least8. This is a computational restriction. The native enumerations and solver exclusion do not have a complete Lean contradiction certificate. No globalQ8/Q9upper bound follows.

## Actual construction search

All1440 endpoint-preserving placements of the applicable97-edge truncation of the published98-edgeQ8seed were compared with the original95-edge path. The maximum shared vertex count is52, giving an explicit replacement that omits44old vertices and adds46. A120second overlap-maximization run in the degree/square relaxation returned exactly this supplied path. It is connected and all pairs were checked, but no closer path or nearest-path optimality was established. The relaxation's objective bound96 does not strengthen the independent minimum-six-omission restriction.

This returned path has30forbidden overlaps with the first context's outer paths. It gives no193-edgeQ9construction. The finite search range for the minimum number of omissions is therefore computationally6 through44, with the lower end retaining the certificate qualification. The upper end is an explicit known-seed witness. Do not call this a new97-edge record or a newQ9snake.

## Manuscript-wide review

Two read-only reviewers covered all7820lines of the round189 main manuscript and all630lines of the short explanation. The root inspected and applied all actionable findings. The receipt records exact reviewed source hashes and20specific revisions: archived235 qualification, current(15,14,14,14) profile, historical-floor labels, nontrivial-path/window domains, nonnegative potential parameters, exact two-edge gain scope, larger contiguous replacements remaining open, and archive citations for rounds188/189. This is a complete source consistency and presentation review, not an independent verification or rebuild of every proof. Next scheduled review: round200.

## Resume direction and preserved work

Search six-omission replacements, or larger contiguous and coordinated changes with revised crossing ports. Use component balance to organize the deleted intervals and added components. Check any new97-edge path against all84surrounding configurations; then vary outer paths if necessary. Do not repeat unchanged timed-out circuit or optimization queries.

No new longerQ9snake, global upper bound or proof of196 was obtained. The inherited round187 upper-bound checkpoint is unchanged:93/98clause batches; conditional233/234; archived235 still awaits a full independent rebuild. Round188's directQ8all-pairs Lean recheck remains pending. The goal pauses after publication at the user's request.
'''
(H/'MATHEMATICAL_NOTE.md').write_text(note,encoding='utf-8',newline='\n')
(H/'README.md').write_text('''# Round 190: component balance and five-omission restrictions

The requested round is complete. Pause after publication; do not continue without a resume instruction.

The general replacement identity is e(A)=e(D)+delta, and deleted/added path forests have the same number of components. The finite accounting and conditional arithmetic pass Lean. The arbitrary-path integration remains written.

All five-omission replacements of the common95-edge path are computationally excluded: the one-interval case was known,16020two-interval placements are now exhausted, and a degree/square relaxation excludes three-or-more intervals. Minimum6omissions/8additions for a97-edge fixed-port replacement; complete Lean contradiction certificate pending. The final search returned only the supplied known97-edge seed, omitting44old vertices and incompatible with the firstQ9context. No new record or global bound.

Read [the argument](MATHEMATICAL_NOTE.md), [completion](data/completion.json), [manuscript review](data/manuscript-review.json), [two-interval enumeration](data/two-intervals-five-omissions.json), [degree/square exclusion](data/five-omissions-cycle-cuts.json), and [nearest search](data/nearest-replacement.json).
''',encoding='utf-8',newline='\n')
handoff='''# Round 190 complete; pause after publication

The user explicitly requested pausing after this round. Finish publication and pause the goal. Do not start round191 without a new resume request.

The current direction is dimension-lifting constructions. Read milestones/190-exchange-constraints/MATHEMATICAL_NOTE.md and data/completion.json. For same-endpoint induced paths, with D omitted and A added, e(A)=e(D)+delta and D,A have equal component counts. Lean checks the finite edge identities and arithmetic under explicit degree/size premises; the arbitrary-path integration remains written.

The common95-edge component cannot gain two edges through at most five omissions according to the combined native computations. One interval is covered by round189. Round190 exhausts16020two-interval five-omission placements, including middle-chain reversal and every possible connector-length pair. The remaining3–5interval cases are excluded by a degree/square relaxation (1792squares, zero dynamic cycle cuts,3.062seconds). No complete Lean contradiction certificate. Minimum6omissions and8additions is a computational local restriction, not a global bound.

The nearest search returned exactly the supplied known97-edge seed:52common vertices,44omissions,30forbidden overlaps with the first surrounding context. All pairs pass, but no new closer97path, nearest-path optimality or193-edgeQ9snake. The next new search is six omissions, or larger contiguous/coordinated changes and altered ports. Compare anynew97path with all84contexts.

All search and proof processes are terminal. Preserve models, finite-search ranges and failed proof snapshots. Do not repeat unchanged120second general-five or nearest queries, or the60second circuit two-interval case; the latter is superseded by complete native enumeration. One heavy research worker at a time; Lean limits remain1GiB free at startup,768MiB reserve,256MiB private memory.

Manuscript-wide consistency/domain/evidence review completed for all round189source:7820main lines and630short lines;20corrections saved with exact hashes. This is not a full proof rebuild. Next scheduled review200. ExistingD: manuscripts andE: mirrors preserve authors and hypersetup.

Inherited upper-bound work unchanged: round18793/98clause batches (11904/12424), critical floor15 and actual-snake transfer pending; conditional233/234; archived235 independent rebuild pending. Round188directQ8pairwiseLean recheck remains pending. No unconditional bound or proof of196 added.

Fetched research/unconditional-241 atf393c48e5e583e57d3cbb66e4330f960033229b1, without merging or independent rebuild. Preserve unrelated.gitignore and milestones/50-three-count-return/excess-screen/data/critical-family.json edits.
'''
(R/'handoff/CURRENT_STATUS.md').write_text(handoff,encoding='utf-8',newline='\n');(R/'handoff/NEXT_AGENT_PROMPT.md').write_text('Research is to pause after round190 publication. Resume only upon a new user instruction.\n\n'+handoff,encoding='utf-8',newline='\n')
p=R/'README.md';p.write_text('''# Current result after round 190

The requested round is complete; research pauses after publication. Component balance gives e(A)=e(D)+delta for fixed-endpoint replacements. All five-omission replacements of the common95-edge component are now computationally excluded, giving a minimum of6omissions/8additions for a97-edge replacement. The finite exclusions still lack a complete Lean contradiction certificate. No longerQ9snake or global bound was obtained.

The whole-source manuscript consistency review is complete, with archived-bound qualifications, current share profiles, domains, search scopes and citations corrected. Read [round190](milestones/190-exchange-constraints/README.md), [the argument](milestones/190-exchange-constraints/MATHEMATICAL_NOTE.md), [handoff](handoff/CURRENT_STATUS.md), [paper](paper/snake9_research.tex), and [frontier explanation](paper/snake9_frontier_explanation.tex).

## Earlier checkpoints

'''+p.read_text(),encoding='utf-8',newline='\n')
(H/'scripts/publication.py').write_text((P/'scripts/publication.py').read_text().replace('Round189','Round190'),encoding='utf-8',newline='\n');(H/'scripts/close.py').write_bytes(Path(__file__).read_bytes())
print(json.dumps({'accepted_modules':len(accepted),'dependency_reports':sum(x['reports'] for x in accepted),'failed_attempts':len(failed),'review_completed':True,'pause_after_publication':True,'manuscripts':[sha(O/n) for n in [main.name,short.name]]},indent=2))
