"""Freeze round 226 evidence and the active construction handoff."""
from pathlib import Path
from datetime import datetime, timezone
import hashlib, json, re, subprocess
H=Path(__file__).resolve().parents[1]; R=H.parents[1]
D=Path('D:/Codex/2026-10-13/new-chat/outputs')
def sha(p): return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def read(p): return json.loads(Path(p).read_bytes())
def save(p,x): Path(p).write_text(json.dumps(x,indent=2)+'\n',encoding='utf-8',newline='\n')
s=read(H/'data/search-summary.json')
assert s['complete_through']==43 and len(s['width44_unresolved'])==42
assert not list((H/'data').glob('*.lock'))
native=[]
for p in sorted((H/'data').glob('*-execution.json')):
    a=read(p)
    if 'resource_gate' not in a or 'module' in a: continue
    if a.get('status')!='ACCEPTED_NATIVE_RESULT': continue
    assert a['exit_code']==0 and a['stop_reason'] is None
    assert all(sha(x)==v for x,v in a['pins'].items())
    tag=p.name.removesuffix('-execution.json'); q=H/'data'/(tag+'.json')
    if not q.exists(): q=H/'data'/tag/'result.json'
    assert sha(q)==a['result_sha256']; j=read(q)
    if 'checkpoint_sha256' in j: assert sha(q.with_name('checkpoint.json'))==j['checkpoint_sha256']
    native.append(dict(tag=tag,status=j['status'],receipt_sha256=sha(p),result_sha256=sha(q)))
assert len(native)==11 and {x['tag'] for x in native}==set(s['runs'])
proofs=[]
for name in ['Residual226','ResidualCapacity226','ZeroFace226','FaceCounts226','BoundaryContraction226']:
    p=H/'data'/(name+'-audit.json'); a=read(p)
    assert a['status']=='PASS' and a['exit_code']==0 and a['stop_reason'] is None
    for pk,hk in [('source','source_sha256'),('object','olean_sha256'),('log','log_sha256')]: assert sha(a[pk])==a[hk]
    assert all(sha(x)==v for x,v in a['dependencies'].items())
    assert all(set(q['axioms'])<={'propext','Classical.choice','Quot.sound'} for q in a['axioms'])
    proofs.append(dict(module=name,receipt_sha256=sha(p),reports=len(a['axioms'])))
assert sum(p['reports'] for p in proofs)==15
archive=read(H/'data/model-archive.json'); assert len(archive['files'])==164
assert sha(H/'data'/archive['archive'])==archive['archive_sha256']
assert all(sha(H/'data'/n)==v['sha256'] for n,v in archive['files'].items())
docs={}
for name,receipt in [('snake9_frontier_explanation.tex','frontier-compile-final.json'),('snake9_research.tex','main-compile-final.json')]:
    p=D/name; assert p.read_bytes()==(R/'paper'/name).read_bytes()
    before=(H/'data'/(name+'.before.txt')).read_text(encoding='utf-8'); after=p.read_text(encoding='utf-8')
    assert re.search(r'\\author\{[^\n]*',before).group()==re.search(r'\\author\{[^\n]*',after).group()
    if name=='snake9_research.tex': assert re.search(r'\\hypersetup\{.*?\n\}',before,re.S).group()==re.search(r'\\hypersetup\{.*?\n\}',after,re.S).group()
    labels=re.findall(r'\\label\{([^}]+)\}',after); assert len(labels)==len(set(labels))
    assert set(re.findall(r'\\label\{([^}]+)\}',before))<=set(labels)
    assert set(re.findall(r'\\(?:ref|eqref|pageref)\{([^}]+)\}',after))<=set(labels)
    bib=set(re.findall(r'\\bibitem\{([^}]+)\}',after))
    assert {v.strip() for g in re.findall(r'\\cite\{([^}]+)\}',after) for v in g.split(',')}<=bib
    c=read(H/'data'/receipt)
    assert not c.get('isError',False) and any(json.loads(t['text']).get('kind')=='success' for t in c['content'] if t['type']=='text')
    docs[name]=dict(editor=str(p),mirror=str(R/'paper'/name),sha256=sha(p),compile_sha256=sha(H/'data'/receipt))
review=(H/'logs/review-final-documents.md').read_text(encoding='utf-8')
assert all(x['sha256'] in review for x in docs.values()) and sha(H/'MATHEMATICAL_NOTE.md') in review
save(H/'data/document-verification.json',dict(documents=docs,scope='Exact mirrors, preserved authors/settings, references, bounded independent source review and successful built-in compilation; no PDF page-by-page review.'))
previous=read(R/'milestones/225-replacement-widths/data/completion.json')
for x in previous['frozen_parent_search_states'].values(): assert sha(R/x['path'])==x['sha256']
git=['git','-c','core.commitGraph=false','-c','maintenance.auto=false','-c','gc.auto=0']
contributor=subprocess.check_output(git+['rev-parse','origin/research/unconditional-241'],cwd=R,text=True).strip()
completion=dict(round=226,status='PROGRESS',previous_round_status=previous['status'],goal_status='ACTIVE',started_utc='2026-11-15 07:33:23 UTC',finished_utc=datetime.now(timezone.utc).isoformat(),interval=[191,233],new_q9_record=False,new_global_bound=False,complete_replacement_width=43,unresolved44=s['width44_unresolved'],shared_q8_contexts=s['shared_q8_contexts'],shared_q8_status='PREPARED_SHARED_SEARCH',solver_exclusions_lean_certified=False,proofs=proofs,native_runs=native,model_count=164,model_archive_sha256=archive['archive_sha256'],search_summary_sha256=sha(H/'data/search-summary.json'),coverage43_sha256=sha(H/'data/coverage43.json'),shared_q8_plan_sha256=sha(H/'data/shared-q8-plan.json'),documents=docs,contributor_revision=contributor,independent_233_rebuild=False,frozen_parent_search_states=previous['frozen_parent_search_states'])
save(H/'data/completion.json',completion)
handoff=f'''# Current state after round 226

Goal ACTIVE. Continue construction research; coworkers handle upper bounds. Read milestones/226-connected-replacement-search/MATHEMATICAL_NOTE.md and data/completion.json. No new snake or global bound.

The selected endpoint-24 construction is computationally excluded for two replacement blocks of at most 43 edges. All 294 maximal width-43 contexts are covered. Of the 301 width-44 contexts, 42 remain unresolved: the initial 92 were reduced by 46 boundary/face exclusions and four complete two-port covers. Solver contradictions have no Lean replay. See coverage43.json, combined44.json and search-summary.json.

Seed normalized bank 123, endpoints 0/88, append 24, blockers index 7/value 28 and index 143/value 56. Retain outside indices and anchors. Target 193 vertices and four bit-8 crossings. Width-w maximal intervals are [a,a+w], a=0..6, and [c,c+w], c=144-w..142. This family does not impose the earlier 193 closure or mutual-contact premise. Its exclusion is local to the fixed seed and construction.

Priority next search: contexts 194,195,196,197,198,199,201 have the same 109-vertex first lower domain. Find a 43-edge induced Q8 path from 18 to 224, then append 480. Their first interval is [4,48]. Each needs a compatible 44-edge second replacement with two bit-8 crossings. The alternative suffix [488,480] has been excluded in all seven. Exact domains and copied rows are in shared-q8-plan.json. This common search is prepared, not executed. Grow each common first prefix once; reject it only when every second context fails a necessary condition. At a complete first path, search the surviving second contexts and audit the entire 193-vertex Q9 path. The other 35 unresolved contexts remain separate.

The boundary rule uses completed width-43 exclusion: a valid width-44 pair must change both original boundary-adjacent vertices of at least one block. Otherwise trim one unchanged boundary from each block to obtain an excluded width-43 representation of the same path. Selecting an original anchor-neighbour forces it to occupy that adjacent position. The concrete exclusion premise is native; the contraction implication is Lean checked.

Accepted Lean modules: Residual226, ResidualCapacity226, ZeroFace226, FaceCounts226, BoundaryContraction226 (15 reports). They check path separation/closed-set containment, capacity implications, zero-crossing constancy, literal face counts and conditional boundary contraction. They do not check the solver contradictions, native component extraction, Tarjan decomposition or traversal. Read their accepted receipts and dependencies.

All 11 native runs and compiler processes are terminal. Both direct DFS frontiers remain incomplete and preserved; their width-43 contexts 22 and 114 were subsequently excluded by separate complete native covers. Do not resume them as open cases. The context-22 transfer changes only the pinned source path and is recorded in checkpoint-transfer.json. All 164 raw models remain local and their exact bytes are archived in solver-models.zip.

Maintained interval 191 <= a(9) <= 233; independent 233 rebuild remains pending. Contributor revision {contributor} is work in progress toward 231; no new global bound is imported. Preserve fixed-parent round-222 result and frozen historical cases 22/23/24/9 in rounds 217/211/209/209; only [1,4] is exhausted among 28 six-coordinate choices. Do not rerun closed unchanged families.

Workdir E:/Snake-in-a-box. Python C:/Users/hironakaiori/.cache/codex-runtimes/codex-primary-runtime/dependencies/python/python.exe with -B -X utf8. One heavy worker; startup >=1 GiB, reserve >=768 MiB, private <=256 MiB; native thread variables all 1. Lean 60 s, -j1 -s8192. Preserve live handles. Editor originals D:/Codex/2026-10-13/new-chat/outputs/snake9_research.tex and snake9_frontier_explanation.tex; exact mirrors in paper/. Preserve authors and hypersetup. Compile frontier then main. Full main review last 220, next 230. Preserve unrelated .gitignore and milestone-50 edits. Publish only the exact scoped manifest, with Git maintenance disabled and bounded pack memory.
'''
(R/'handoff/CURRENT_STATUS.md').write_text(handoff,encoding='utf-8',newline='\n')
(R/'handoff/NEXT_AGENT_PROMPT.md').write_text('Continue the active construction goal from round 226. Read CURRENT_STATUS.md and the round-226 mathematical note and accepted evidence. Implement the shared Q8 first-path search for contexts 194-199 and 201, using data/shared-q8-plan.json. Retain a prefix whenever any second context remains possible. Audit any assembled 193-vertex Q9 witness independently. The 42 unresolved width-44 contexts are local to this construction; coworkers handle global upper bounds. Preserve historical checkpoints and publish each productive round.\n',encoding='utf-8',newline='\n')
p=R/'README.md'; old=p.read_text(encoding='utf-8'); assert old.startswith('# Current result after round 225')
p.write_text('''# Current result after round 226

The selected endpoint-24 construction is computationally excluded for two replacement blocks of at most 43 edges. Width 44 leaves 42 contexts unresolved. A conditional boundary-change rule and face/port restrictions remove 50 of the previous 92 cases. Seven survivors share exactly one 109-vertex Q8 domain: the next target is a 43-edge induced path from 18 to 224, followed by 480 and a compatible second replacement. Five Lean modules check supporting implications and literal face counts; numerical solver exclusions retain their native status. No new snake or global bound. Goal ACTIVE.

Read [the argument](milestones/226-connected-replacement-search/MATHEMATICAL_NOTE.md), [evidence](milestones/226-connected-replacement-search/data/completion.json), [handoff](handoff/CURRENT_STATUS.md), and [short explanation](paper/snake9_frontier_explanation.tex).

## Earlier checkpoints

'''+old,encoding='utf-8',newline='\n')
print('FINALIZED_ROUND226',len(proofs),'proof modules',len(native),'native runs')
