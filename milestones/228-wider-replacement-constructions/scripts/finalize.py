"""Freeze round 228 evidence and its active construction handoff."""
from pathlib import Path
from datetime import datetime,timezone
import hashlib,json,re,subprocess
H=Path(__file__).resolve().parents[1];R=H.parents[1];D=Path('D:/Codex/2026-10-13/new-chat/outputs')
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def read(p):return json.loads(Path(p).read_bytes())
def save(p,j):Path(p).write_text(json.dumps(j,indent=2)+'\n',encoding='utf-8',newline='\n')
s=read(H/'data/search-summary.json');coverage=read(H/'data/coverage45.json')
assert s['complete_through']==45 and not s['width45_unresolved']
assert sha(H/'data/coverage45.json')==s['coverage_sha256']
assert all(sha(p)==h for p,h in coverage['pins'].items())
assert not list((H/'data').glob('*.lock'))
native=[]
for run in s['runs']:
    tag=run['tag'];ep=H/'data'/(tag+'-execution.json');e=read(ep)
    rp=H/'data'/tag/'result.json' if tag.startswith('reduced') else H/'data'/(tag+'.json')
    assert e['status']=='ACCEPTED_NATIVE_RESULT' and e['exit_code']==0 and e['stop_reason'] is None
    assert all(sha(p)==h for p,h in e['pins'].items()) and sha(rp)==e['result_sha256']
    assert sha(ep)==run['receipt_sha256'] and sha(rp)==run['result_sha256']
    native.append(run)
partial=read(H/'data/boundary45-execution.json')
assert partial['status']=='INTERRUPTED' and partial['stop_reason']=='LOW_FREE_MEMORY'
assert all(sha(p)==h for p,h in partial['pins'].items())
assert sha(H/'data/boundary45.json')==partial['result_sha256']
proof=read(H/'data/AllocationFacts228-audit.json')
assert proof['status']=='PASS' and proof['exit_code']==0 and proof['stop_reason'] is None
for pk,hk in [('source','source_sha256'),('object','olean_sha256'),('log','log_sha256')]:assert sha(proof[pk])==proof[hk]
assert all(sha(p)==h for p,h in proof['dependencies'].items())
assert len(proof['axioms'])==3 and all(set(r['axioms'])<={'propext','Classical.choice','Quot.sound'} for r in proof['axioms'])
archive=read(H/'data/model-archive.json');assert len(archive['files'])==416
assert sha(H/'data'/archive['archive'])==archive['archive_sha256']
assert all(sha(H/'data'/p)==h['sha256'] for p,h in archive['files'].items())
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
    c=read(H/'data'/receipt)
    assert not c.get('isError',False) and any(json.loads(t['text']).get('kind')=='success' for t in c['content'] if t['type']=='text')
    docs[name]=dict(editor=str(p),mirror=str(R/'paper'/name),sha256=sha(p),compile_sha256=sha(H/'data'/receipt))
review=(H/'logs/review-final-documents.md').read_text(encoding='utf-8')
assert all(r['sha256'] in review for r in docs.values()) and sha(H/'MATHEMATICAL_NOTE.md') in review
save(H/'data/document-verification.json',dict(documents=docs,scope='Exact mirrors, authors/settings preserved, references, independent bounded source review and successful built-in compilation. No page-by-page PDF review.'))
previous=read(R/'milestones/227-shared-q8-construction/data/completion.json')
for r in previous['frozen_parent_search_states'].values():assert sha(R/r['path'])==r['sha256']
git=['git','-c','core.commitGraph=false','-c','maintenance.auto=false','-c','gc.auto=0']
contributor=subprocess.check_output(git+['rev-parse','origin/research/unconditional-241'],cwd=R,text=True).strip()
completion=dict(round=228,status='PROGRESS',previous_round_status=previous['status'],goal_status='ACTIVE',started_utc='2026-11-15 14:12:54 UTC',finished_utc=datetime.now(timezone.utc).isoformat(),interval=[191,233],new_q9_record=False,new_global_bound=False,complete_replacement_width=45,width45_contexts=308,unresolved45=[],counts=s['counts'],reduced_queries=331,direct_queries=13,partial_batch_terminal_exclusions=34,interrupted_initial_batch=dict(status=partial['status'],reason=partial['stop_reason']),solver_exclusions_lean_certified=False,proofs=[dict(module='AllocationFacts228',reports=3,receipt_sha256=sha(H/'data/AllocationFacts228-audit.json'))],native_runs=native,model_count=416,model_archive_sha256=archive['archive_sha256'],coverage45_sha256=sha(H/'data/coverage45.json'),documents=docs,contributor_revision=contributor,independent_233_rebuild=False,greedy_experiment_executed=False,frozen_parent_search_states=previous['frozen_parent_search_states'])
save(H/'data/completion.json',completion)
handoff=f'''# Current state after round 228

The goal is ACTIVE. The user resumed the construction research, then asked to retain partial greedy growth for a useful later opportunity while continuing the original route. No greedy experiment was run. Read milestones/228-wider-replacement-constructions/MATHEMATICAL_NOTE.md, ROUTE_DECISIONS.md and data/completion.json. Round 228 is PROGRESS; no new snake or global bound.

The fixed-seed endpoint-24 construction is computationally excluded for two length-preserving replacement blocks of at most 45 edges each. All 308 maximal contexts are covered: 107 initial geometric exclusions, 34 completed native rows from an interrupted initial batch, 154 upper-piece reductions (69 empty and 85 covered by 331 unique path-pair queries), and 13 direct queries. Exact maps are in data/coverage45.json. Smaller blocks are covered by padding, never by transferring a smaller exclusion upward.

Seed normalized bank123, endpoints0/88, append24, blockers index7/value28 and index143/value56. Retain all outside positions and both anchors of each block. Require193vertices and four coordinate-8 crossings. Maximal width45 intervals [a,a+45], a=0..6, and [c,c+45], c=99..142. Other seeds, endpoints, crossing counts, three-block and length-changing replacements remain outside the exclusion.

The boundary cut uses the complete native width44 premise: one width45block must omit both its old anchor neighbours; otherwise trim one unchanged boundary edge in each block to the excluded family. It is valid at width45 only with that premise. The copied direct worker accepts a width argument but does NOT validate arbitrary wider-width cuts. For width46 supply the new width45 premise and update/guard the worker before use.

154contexts have unique crossing allocations (0,1):16, (0,2):24, (1,1):78, (1,2):36. Each replacement has one lower segment. Enumerating upper portions gives2141configs; instantiate the boundary disjunction before deduplication:4282branches,3527fixedboundaryconflicts,83disconnections,672survivors,392exactgroups,331representatives. All331reducedtasks and13directtasks are natively infeasible at their first solve without cyclecuts. Initial reduced batch321infeasible+10unknown; longer retry of exactly those10 closes them. Contexts78-85 and122-126 need direct models because of alternative allocations.

The initial boundary45 batch was INTERRUPTED/LOW_FREE_MEMORY. Its34alreadyterminalinfeasible rows alone were harvested;27unknown,1running andunattemptedrows stayedopen until later resolved. Do not relabel the interrupted batch as accepted. All childprocesses are terminal, no active locks,416rawmodels retained locally and in solver-models.zip. Nothing in the closed width45family needs rerunning.

AllocationFacts228 has PASS with3reports:154literalrows, finite allocation verification, and arbitrary natural crossing counts forced by total/parity/zero-permission premises. Only allocation arithmetic is kernel checked. Actual-path parity/capacity and gluing reuse earlier checked results; extraction, domain necessity, complete enumeration, context assembly and solver contradictions retain native scope. No end-to-end Lean cover certificate.

Generic projection-mask limitation: prepare_lower_pairs.py exempts both lower anchors from own upper projections; only actual vertical joining ports should be exempt. Independent enumeration found zero offending contacts in all2141original and672finaltemplates, so this literal round is unaffected. Before wider/new data reuse, fix the mask in a NEW milestone/source without changing pinned228sources. For an upper prefix use first lower endpoint as a port; for an upper suffix use last lower endpoint; absent arms contribute no port. Cross-block projection exclusions remain complete. The final193vertex audit remains mandatory for any candidate.

Next useful construction step: prepare width46 with exact actual-port masks and the new preceding-width boundary premise, then inspect domain/template sizes before committing to expensive solves. The reduction remains useful when both blocks cross once. If wider cases merely reproduce excluded lower tasks or costs rise without a new structural possibility, change endpoint or seed. Partial greedy growth is retained as an alternative: preserve an interior core and regrow both ends with limited backtracking. Do not retry unchanged one-ended regrowth of the already-excluded112vertexprefixes. Firsttarget192edges;196remainsconjectural. Coworkers handle globalupperbounds.

Maintained interval 191<=a(9)<=233; independent 233 rebuild pending. Contributor revision {contributor} was fetched at closing. Commit summaries describe a Lean 4.35 floor port and resource guards; neither the port nor a new contributor bound was independently rebuilt or imported in this round. Preserve fixed-parent222 and frozen history cases22/23/24/9 in217/211/209/209. Only[1,4] exhausted among28six-coordinatechoices.

Workdir E:/Snake-in-a-box. Python C:/Users/hironakaiori/.cache/codex-runtimes/codex-primary-runtime/dependencies/python/python.exe with -B -X utf8. Oneheavyworker; startup>=1GiB,reserve>=768MiB,private<=256MiB; threadenvall1. Lean60s,-j1,-s8192. Do not restart live handles. Editor originals D:/Codex/2026-10-13/new-chat/outputs/snake9_research.tex and snake9_frontier_explanation.tex; exactmirrors paper/. Authors andhypersetuppreserved. Compilefrontierthenmain. Fullmainreviewlast220,next230. Preserve unrelated.gitignore andmilestone50edits. Exactscopedmanifestpublicationonly; Gitmaintenanceoff,boundedpackmemory.
'''
(R/'handoff/CURRENT_STATUS.md').write_text(handoff,encoding='utf-8',newline='\n')
(R/'handoff/NEXT_AGENT_PROMPT.md').write_text('Goal ACTIVE. Read CURRENT_STATUS.md and round228 evidence. Native two-block exclusion now complete through45. Next consider width46 after correcting actual-port masks in a new milestone and replacing the boundary-cut premise with coverage45; inspect reduced tasks before expensive search. Do not rerun closed contexts or original112vertexprefix regrowth. Greedy growth is parked for later usefulness. Keep construction work separate from coworkers globalbounds, preserve all frozen histories, authors and hyperlink settings.\n',encoding='utf-8',newline='\n')
p=R/'README.md';old=p.read_text(encoding='utf-8');assert old.startswith('# Current result after round 227')
p.write_text('''# Current result after round 228

The selected endpoint-24 construction is computationally excluded for two length-preserving replacement blocks of at most 45 edges. All 308 maximal contexts are covered. Fixing the small upper-face portions reduces 154 contexts to lower-dimensional tasks, including cases where both replacements cross the chosen coordinate. All 331 representative tasks and thirteen direct queries are natively infeasible. Lean checks the 154 literal crossing-allocation records and their arithmetic implication; enumeration and solver contradictions retain native status. No new snake or global bound. The construction goal remains active, with partial greedy growth reserved for later use.

Read [the argument](milestones/228-wider-replacement-constructions/MATHEMATICAL_NOTE.md), [complete cover](milestones/228-wider-replacement-constructions/data/coverage45.json), [evidence](milestones/228-wider-replacement-constructions/data/completion.json), [handoff](handoff/CURRENT_STATUS.md), and [short explanation](paper/snake9_frontier_explanation.tex).

## Earlier checkpoints

'''+old,encoding='utf-8',newline='\n')
print('FINALIZED_ROUND228',len(native),'accepted native runs; initial interrupted batch preserved; goal ACTIVE')
