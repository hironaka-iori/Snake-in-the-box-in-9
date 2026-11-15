"""Freeze round230 evidence and the requested pause handoff."""
from pathlib import Path
from datetime import datetime,timezone
from collections import Counter
import hashlib,json,re,subprocess
H=Path(__file__).resolve().parents[1];R=H.parents[1];D=Path('D:/Codex/2026-10-13/new-chat/outputs')
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def read(p):return json.loads(Path(p).read_bytes())
def save(p,j):Path(p).write_text(json.dumps(j,indent=2)+'\n',encoding='utf-8',newline='\n')
coverage=read(H/'data/coverage-free46.json');two=read(H/'data/coverage-two46.json')
for c in [coverage,two]:
    assert c['status']=='COMPLETE_NATIVE_EXCLUSION' and c['contexts']==315
    assert all(sha(p)==h for p,h in c['pins'].items())
assert not coverage['unresolved'] and not list((H/'data').glob('*.lock'))
native=[]
for tag,name in [('lower-preparation','lower-pairs.json'),('two-pairs','two-pairs/result.json'),('visits46','visits46.json')]:
    ep=H/'data'/(tag+'-execution.json');e=read(ep)
    assert e['status']=='ACCEPTED_NATIVE_RESULT' and e['exit_code']==0 and e['stop_reason'] is None
    assert all(sha(p)==h for p,h in e['pins'].items()) and sha(H/'data'/name)==e['result_sha256']
    for stream in ['stdout','stderr']:assert sha(H/'logs'/(tag+'-'+stream+'.log'))==e[stream+'_sha256']
    native.append(dict(tag=tag,receipt_sha256=sha(ep),result_sha256=sha(H/'data'/name)))
a=read(H/'data/FaceVisits230-audit.json')
assert a['status']=='PASS' and a['exit_code']==0 and a['stop_reason'] is None
for pk,hk in [('source','source_sha256'),('object','olean_sha256'),('log','log_sha256')]:assert sha(a[pk])==a[hk]
assert all(sha(p)==h for p,h in a['dependencies'].items())
assert len(a['axioms'])==3 and all(set(x['axioms'])<={'propext','Classical.choice','Quot.sound'} for x in a['axioms'])
archive=read(H/'data/model-archive.json');assert len(archive['files'])==26
assert sha(H/'data'/archive['archive'])==archive['archive_sha256']
assert all(sha(H/'data'/p)==x['sha256'] for p,x in archive['files'].items())
docs={}
for name,receipt in [('snake9_frontier_explanation.tex','frontier-compile-final.json'),('snake9_research.tex','main-compile-final.json')]:
    p=D/name;assert p.read_bytes()==(R/'paper'/name).read_bytes()
    before=(H/'data'/(name+'.before.txt')).read_text(encoding='utf-8');after=p.read_text(encoding='utf-8')
    assert re.search(r'\\author\{[^\n]*',before).group()==re.search(r'\\author\{[^\n]*',after).group()
    if name=='snake9_research.tex':assert re.search(r'\\hypersetup\{.*?\n\}',before,re.S).group()==re.search(r'\\hypersetup\{.*?\n\}',after,re.S).group()
    labels=re.findall(r'\\label\{([^}]+)\}',after);assert len(labels)==len(set(labels))
    assert set(re.findall(r'\\label\{([^}]+)\}',before))<=set(labels)
    assert set(re.findall(r'\\(?:ref|eqref|pageref)\{([^}]+)\}',after))<=set(labels)
    bib=set(re.findall(r'\\bibitem\{([^}]+)\}',after))
    assert {v.strip() for g in re.findall(r'\\cite\{([^}]+)\}',after) for v in g.split(',')}<=bib
    pattern=r'\\begin\{(theorem|proposition|lemma|corollary|conjecture|definition|remark|proof)\}.*?\\end\{\1\}'
    old=Counter(m.group(0) for m in re.finditer(pattern,before,re.S));new=Counter(m.group(0) for m in re.finditer(pattern,after,re.S));assert old<=new
    c=read(H/'data'/receipt);assert not c.get('isError',False)
    assert any(json.loads(t['text']).get('kind')=='success' for t in c['content'] if t['type']=='text')
    docs[name]=dict(editor=str(p),mirror=str(R/'paper'/name),sha256=sha(p),compile_sha256=sha(H/'data'/receipt))
review=(H/'logs/review-final-documents.md').read_text(encoding='utf-8')
assert all(x['sha256'] in review for x in docs.values()) and sha(H/'MATHEMATICAL_NOTE.md') in review
save(H/'data/document-verification.json',dict(documents=docs,full_review='logs/full-manuscript-review.md',full_review_applied=True,next_full_review_round=240,scope='Full incoming source review; guarded editorial revision applied before230 additions; unchanged earlier mathematical statements/proofs, labels, authors/hypersetup; exact editor mirrors; final bounded source review and successful built-in compilation. No page-by-page PDF review.'))
previous=read(R/'milestones/229-two-layer-construction/data/completion.json')
for x in previous['frozen_parent_search_states'].values():assert sha(R/x['path'])==x['sha256']
git=['git','-c','core.commitGraph=false','-c','maintenance.auto=false','-c','gc.auto=0']
contributor=subprocess.check_output(git+['rev-parse','origin/research/unconditional-241'],cwd=R,text=True).strip()
completion=dict(round=230,status='PROGRESS',goal_status='PAUSE_REQUESTED_AFTER_PUBLICATION',started_utc='2026-11-15 15:01:59 UTC',finished_utc=datetime.now(timezone.utc).isoformat(),interval=[191,233],new_q9_record=False,new_global_bound=False,complete_any_crossing_width=46,contexts=315,unresolved=[],native_runs=native,proofs=[dict(module='FaceVisits230',reports=3,receipt_sha256=sha(H/'data/FaceVisits230-audit.json'))],actual_path_to_runs_lean_checked=False,solver_exclusions_lean_certified=False,coverage_free46_sha256=sha(H/'data/coverage-free46.json'),coverage_two46_sha256=sha(H/'data/coverage-two46.json'),model_count=26,model_archive_sha256=archive['archive_sha256'],documents=docs,full_manuscript_review_round=230,next_full_manuscript_review_round=240,contributor_revision=contributor,independent_233_rebuild=False,frozen_parent_search_states=previous['frozen_parent_search_states'])
save(H/'data/completion.json',completion)
handoff=f'''# Current state after round 230

The user requested a pause after this round. This checkpoint closes the round; resume research only on a new user instruction. Round 230 is PROGRESS, with no new snake or global upper bound. Read milestones/230-two-crossing-frontier/MATHEMATICAL_NOTE.md and data/completion.json.

Workdir E:/Snake-in-a-box. The selected bank123 construction is now natively excluded through two length-preserving replacement blocks of 46 edges for every crossing count. It appends 24 after endpoint 88, retains the two block anchors and all outside indices, and uses maximal intervals [a,a+46], a=0..6 and [b,b+46], b=98..142. There are 315 contexts. Padding covers shorter blocks. This restricted family conclusion is not a universal snake theorem.

The prior round-229 unrestricted cover excluded 304 contexts: 106 geometric and 198 native. Its eleven residual IDs were 34,38,39,40,79,83,84,124,126,128,129. Exactly two crossings force allocations (0,0) in the first four and (1,0) in the other seven. Complete upper enumeration gives 15 lower path-pair tasks, all INFEASIBLE without a boundary-change cut. coverage-two46.json assembles the complete two-crossing cover. The independently observed forced-chain identities 0/4, 1/5, 2/6 were not needed because all 15 tasks ran.

Four and six crossings were already completely excluded in the same family. The nine original six-crossing UNKNOWNs were closed by broader queries without a six-count cut on those nine; do not introduce circularity or rewrite old sources. Since endpoints 0 and 24 share a face and at least one crossing is retained, every remaining candidate would have an even total of at least eight crossings.

FaceVisits230 has three accepted standard-axiom reports: an interior face piece needs at least three vertices; the finite run-list vertex budget; and 3c<=2u+r under explicit incidence and endpoint premises. The written whole-path argument also gives 3c<=2l+2-r, hence 3c<=m+2 for an m-edge path. Extracting maximal runs from an actual path is not implemented in Lean. Two earlier elaboration failures remain archived separately and are not accepted proof receipts. LayerJoining is a verified reused dependency.

The final visits46 worker imposes total crossings at least eight and both face inequalities per replacement. It prescribes no exact crossing count and no boundary change. All eleven queries are INFEASIBLE on their first solve; there are no cycle cuts or witness. coverage-free46.json combines them with the prior 304, giving complete native closure of all 315 contexts. Independent model review reconstructed all 9,115 linear constraints and domains. Enumeration, data extraction and solver contradictions remain native, without end-to-end Lean certification. Do not rerun this closed family unchanged.

Next construction preparation: compare endpoint extension blockers across saved 191-edge seeds, group literal cube-isometry duplicates, then choose a different seed or endpoint with fewer or more localized conflicts. This is an untested hypothesis, not a completed survey or claimed improvement. Wider blocks or length-changing replacements are alternatives. The first target is 192 edges; 196 remains conjectural. Partial greedy growth is reserved for a later suitable subproblem. Coworkers handle global upper bounds. Do not repeat unchanged one-ended regrowth of the excluded 112-vertex prefixes.

The maintained interval is 191<=a(9)<=233; an independent full rebuild of 233 remains pending. Contributor {contributor} was fetched and its current head inspected; no new contributor work was imported or rebuilt. Preserve the round-222 fixed-parent ceiling of 191 and frozen history cases 22/23/24/9 in rounds 217/211/209/209. Only [1,4] is exhausted among 28 six-coordinate choices; other frozen frontiers remain open.

All research workers are terminal. The 26 raw models remain local and exact copies are in this milestone's data/solver-models.zip. The original documents remain D:/Codex/2026-10-13/new-chat/outputs/snake9_research.tex and snake9_frontier_explanation.tex, mirrored exactly in paper/. Both compiled successfully. Full source review was completed in round 230; the next is due at 240. Originals preserve Iori Hironaka, Tommy Ma, Steven Zhan and the complete hypersetup. See the final document review, full review and document-verification receipts. No page-by-page PDF review is claimed.

Resources: one heavy worker or compiler at a time; startup at least 1 GiB free, reserve at least 768 MiB, private memory at most 256 MiB; all native thread variables set to 1. Lean: 60 seconds, -j1, -s8192. Python: C:/Users/hironakaiori/.cache/codex-runtimes/codex-primary-runtime/dependencies/python/python.exe with -B -X utf8. Preserve unrelated .gitignore and milestone-50 edits; use exact scoped publication, Git maintenance off and bounded pack memory. Publication and pausing are administrative closure; this handoff does not authorize the next round.
'''
(R/'handoff/CURRENT_STATUS.md').write_text(handoff,encoding='utf-8',newline='\n')
(R/'handoff/NEXT_AGENT_PROMPT.md').write_text(handoff,encoding='utf-8',newline='\n')
old=(R/'README.md').read_text(encoding='utf-8')
(R/'README.md').write_text('''# Current result after round 230

The selected endpoint-24 construction is computationally excluded through two length-preserving replacement blocks of 46 edges for every crossing count. All 315 maximal contexts are covered. Fifteen exact-two path-pair queries and eleven final face-visit queries close the last cases. Three general face-visit components passed Lean; extraction, enumeration and native solver contradictions retain their stated limits. No longer snake or global bound is obtained. The user requested a pause after this round.

Read [the argument](milestones/230-two-crossing-frontier/MATHEMATICAL_NOTE.md), [complete cover](milestones/230-two-crossing-frontier/data/coverage-free46.json), [evidence](milestones/230-two-crossing-frontier/data/completion.json), [handoff](handoff/CURRENT_STATUS.md), and [short explanation](paper/snake9_frontier_explanation.tex).

## Earlier checkpoints

'''+old,encoding='utf-8',newline='\n')
print('FINALIZED_ROUND230_COMPLETE_NATIVE_FAMILY; PAUSE_REQUESTED')
