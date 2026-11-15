"""Freeze round 227 evidence and the active construction handoff."""
from pathlib import Path
from datetime import datetime, timezone
import hashlib, json, re, subprocess
H=Path(__file__).resolve().parents[1]; R=H.parents[1]
D=Path('D:/Codex/2026-10-13/new-chat/outputs')
def sha(p): return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def read(p): return json.loads(Path(p).read_bytes())
def save(p,x): Path(p).write_text(json.dumps(x,indent=2)+'\n',encoding='utf-8',newline='\n')
s=read(H/'data/search-summary.json')
assert s['complete_through']==44 and len(s['width44_unresolved'])==0
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
assert len(native)==3 and {x['tag'] for x in native}=={x['tag'] for x in s['runs']}
proofs=[]
for name in ['TemplateFacts227']:
    p=H/'data'/(name+'-audit.json'); a=read(p)
    assert a['status']=='PASS' and a['exit_code']==0 and a['stop_reason'] is None
    for pk,hk in [('source','source_sha256'),('object','olean_sha256'),('log','log_sha256')]: assert sha(a[pk])==a[hk]
    assert all(sha(x)==v for x,v in a['dependencies'].items())
    assert all(set(q['axioms'])<={'propext','Classical.choice','Quot.sound'} for q in a['axioms'])
    proofs.append(dict(module=name,receipt_sha256=sha(p),reports=len(a['axioms'])))
assert sum(p['reports'] for p in proofs)==4
archive=read(H/'data/model-archive.json'); assert len(archive['files'])==57
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
previous=read(R/'milestones/226-connected-replacement-search/data/completion.json')
for x in previous['frozen_parent_search_states'].values(): assert sha(R/x['path'])==x['sha256']
git=['git','-c','core.commitGraph=false','-c','maintenance.auto=false','-c','gc.auto=0']
contributor=subprocess.check_output(git+['rev-parse','origin/research/unconditional-241'],cwd=R,text=True).strip()
completion=dict(round=227,status='PROGRESS',previous_round_status=previous['status'],goal_status='PAUSE_AFTER_PUBLICATION_REQUESTED',started_utc='2026-11-15 08:00:16 UTC',finished_utc=datetime.now(timezone.utc).isoformat(),interval=[191,233],new_q9_record=False,new_global_bound=False,complete_replacement_width=44,width44_contexts=301,unresolved44=[],new_context_exclusions=42,reduced_queries=57,solver_exclusions_lean_certified=False,proofs=proofs,native_runs=native,model_count=57,model_archive_sha256=archive['archive_sha256'],search_summary_sha256=sha(H/'data/search-summary.json'),coverage44_sha256=sha(H/'data/coverage44.json'),dfs_superseded=True,atomic_successor_executed=False,documents=docs,contributor_revision=contributor,independent_233_rebuild=False,frozen_parent_search_states=previous['frozen_parent_search_states'])
save(H/'data/completion.json',completion)
handoff=f"""# Current state after round 227

The user requested a pause after this round. Publication is the final work before setting the goal to paused. Do not resume research until requested. Read milestones/227-shared-q8-construction/MATHEMATICAL_NOTE.md and data/completion.json. Round 227 is PROGRESS; no new snake or global bound.

The fixed-seed endpoint-24 construction is computationally excluded for two length-preserving replacement blocks of at most 44 edges each. All 301 maximal contexts are covered. Prior exclusions cover 259; this round excludes the remaining 42 through 57 lower-dimensional path-pair models. See data/coverage44.json for the exact context/configuration/representative mappings. Numerical contradictions remain native, without Lean certificates.

Seed normalized bank 123, endpoints 0/88, append 24, blockers index 7/value 28 and index 143/value 56. Retain outside indices and anchors; require 193 vertices and four coordinate-8 crossings. Maximal width44 intervals [a,a+44], a=0..6, and [c,c+44], c=100..142. Padding covers smaller replacements. Other seeds, endpoints, crossing budgets and length-changing replacements remain outside this exclusion.

Method: enumerate the small upper portions, then search two disjoint nonadjacent induced Q8 paths with prescribed endpoints, lengths and domains. Seven contexts give 18 upper configurations, six exact groups and five representatives after containment. Two groups reconstruct the identical full sequence in all seven contexts. The other35 contexts force first crossing count0 and give230 configurations,79 exactgroups,52 representatives. Every one of the57 new queries is INFEASIBLE at its first solve; no cycle cuts. Initial port232 alternatives remain covered by round226 native evidence.

Accepted new Lean module TemplateFacts227 checks35 concrete face/budget records, two seven-member literal task equalities and configuration17 containment in0. Actual path gluing, parity, zero-face capacity and simultaneous replacement reuse accepted earlier modules. JSON extraction, prepared-domain necessity, finite upper enumeration, complete cover assembly and solver contradictions remain separate native obligations. The initial large proof attempt hit its memory cap and is archived; only the accepted receipt establishes the checked final statement.

The initial120-second common DFS processed5,157,314 prefixes, no completefirstpath, and retained14 pendingprefixes. It is incomplete, now superseded by the native cover. Originalworker interruptions can lose frontier entries; its actual top-of-loop TIME_LIMIT state is unaffected. The atomic successor and exact state transfer are independently reviewed and unexecuted. Do not resume these closed contexts or rerun unchanged width44queries. All childprocesses are terminal and all57 rawmodels remain local, also in exact solver-models.zip.

On a requested resume: the smallest next construction step is width45, applying upper enumeration and exact full-sequence/task deduplication before expensive searches. If it reproduces the same closed tasks, change endpoint or seed instead. A longer snake must be checked over its entire vertex sequence. The first target remains192edges;196 is conjectural. Coworkers handle globalupperbounds.

Maintained interval191<=a(9)<=233, independent233rebuildpending. Contributorrevision {contributor} is ongoing231work, not imported as a completedbound. Preserve fixed-parent222 and frozenhistorycases22/23/24/9 in217/211/209/209; only[1,4] exhausted among28six-coordinatechoices.

Workdir E:/Snake-in-a-box. Python C:/Users/hironakaiori/.cache/codex-runtimes/codex-primary-runtime/dependencies/python/python.exe with -B -X utf8. Oneheavyworker; startup>=1GiB,reserve>=768MiB,private<=256MiB; native threadenvall1. Lean60s,-j1,-s8192. Do not restart live handles. Editor originals D:/Codex/2026-10-13/new-chat/outputs/snake9_research.tex and snake9_frontier_explanation.tex; exact mirrors paper/. Preserve authors/hypersetup. Compilefrontier thenmain. Full mainreviewlast220,next230. Preserve unrelated.gitignore andmilestone50edits. Exact scopedmanifest publication only; Gitmaintenanceoff,boundedpackmemory.
"""
(R/'handoff/CURRENT_STATUS.md').write_text(handoff,encoding='utf-8',newline='\n')
(R/'handoff/NEXT_AGENT_PROMPT.md').write_text('The user requested a pause after round227. Resume only on request. Read CURRENT_STATUS.md and round227 evidence. The selected two-block family is closed through width44; do not resume its superseded DFS. Consider width45 with small-upper-face enumeration first, or change the endpoint/seed if equivalent closed tasks recur. Keep construction work separate from coworkers global bounds. Preserve historical frontiers, authors and hyperlink settings.\n',encoding='utf-8',newline='\n')
p=R/'README.md';old=p.read_text(encoding='utf-8');assert old.startswith('# Current result after round 226')
p.write_text("""# Current result after round 227

The selected endpoint-24 construction is computationally excluded for two length-preserving replacement blocks of at most 44 edges. All 301 maximal width-44 contexts are covered. Fixing small upper-face portions reduces the last 42 contexts to 57 Q8 path-pair queries, all natively infeasible. Literal face and crossing conditions, repeated-task equalities and one domain containment are kernel checked; enumeration and solver contradictions retain native status. No new snake or global bound. The user requested a pause after publication.

Read [the argument](milestones/227-shared-q8-construction/MATHEMATICAL_NOTE.md), [complete cover](milestones/227-shared-q8-construction/data/coverage44.json), [evidence](milestones/227-shared-q8-construction/data/completion.json), [handoff](handoff/CURRENT_STATUS.md), and [short explanation](paper/snake9_frontier_explanation.tex).

## Earlier checkpoints

"""+old,encoding='utf-8',newline='\n')
print('FINALIZED_ROUND227',len(proofs),'proof modules',len(native),'native runs')
