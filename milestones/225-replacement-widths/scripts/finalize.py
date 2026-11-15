"""Freeze the current evidence and active construction handoff."""
from pathlib import Path
from datetime import datetime,timezone
import hashlib,json,re,subprocess
H=Path(__file__).resolve().parents[1];R=H.parents[1];D=Path('D:/Codex/2026-10-13/new-chat/outputs')
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def read(p):return json.loads(Path(p).read_bytes())
def save(p,x):Path(p).write_text(json.dumps(x,indent=2)+'\n',encoding='utf-8',newline='\n')
assert not (H/'data/forest-search.lock').exists()
s=read(H/'data/search-summary.json');assert s['complete_through']==42 and len(s['widths'][-1]['unresolved'])==25
native=[]
for p in sorted((H/'data').glob('*-execution.json')):
    a=read(p)
    if 'resource_gate' not in a:continue
    assert a['status']=='ACCEPTED_NATIVE_RESULT' and a['exit_code']==0 and a['stop_reason'] is None
    assert all(sha(x)==v for x,v in a['pins'].items())
    tag=p.name.removesuffix('-execution.json');result=H/'data'/(tag+'.json')
    if not result.exists():result=H/'data'/tag/'result.json'
    assert sha(result)==a['result_sha256'];j=read(result)
    if 'checkpoint_sha256' in j:assert sha(result.with_name('checkpoint.json'))==j['checkpoint_sha256']
    native.append(dict(tag=tag,status=j['status'],receipt_sha256=sha(p),result_sha256=sha(result)))
proofs=[]
for name in ['ReplacementIndices225','ReplacementCases225','ReplacementPairs225','EndpointParity225','ReplacementConditions225','ReplacementOrdered225','Simultaneous225','IntervalEnlargement225']:
    p=H/'data'/(name+'-audit.json')
    if not p.exists():continue
    a=read(p);assert a['status']=='PASS' and a['exit_code']==0 and a['stop_reason'] is None
    for pk,hk in [('source','source_sha256'),('object','olean_sha256'),('log','log_sha256')]:assert sha(a[pk])==a[hk]
    assert all(sha(x)==v for x,v in a['dependencies'].items())
    assert all(set(q['axioms'])<={'propext','Classical.choice','Quot.sound'} for q in a['axioms'])
    proofs.append(dict(module=name,receipt_sha256=sha(p),reports=len(a['axioms'])))
assert any(p['module']=='Simultaneous225' for p in proofs)
archive=read(H/'data/model-archive.json');assert len(archive['files'])==538
assert sha(H/'data'/archive['archive'])==archive['archive_sha256']
assert all(sha(H/'data'/n)==v['sha256'] for n,v in archive['files'].items())
docs={}
for name,receipt in [('snake9_frontier_explanation.tex','frontier-compile-final.json'),('snake9_research.tex','main-compile-final.json')]:
    p=D/name;assert p.read_bytes()==(R/'paper'/name).read_bytes()
    before=(H/'data'/(name+'.before.txt')).read_text(encoding='utf-8');after=p.read_text(encoding='utf-8')
    assert re.search(r'\\author\{[^\n]*',before).group()==re.search(r'\\author\{[^\n]*',after).group()
    if name=='snake9_research.tex':assert re.search(r'\\hypersetup\{.*?\n\}',before,re.S).group()==re.search(r'\\hypersetup\{.*?\n\}',after,re.S).group()
    labels=re.findall(r'\\label\{([^}]+)\}',after);assert len(labels)==len(set(labels))
    assert set(re.findall(r'\\label\{([^}]+)\}',before))<=set(labels)
    assert set(re.findall(r'\\(?:ref|eqref|pageref)\{([^}]+)\}',after))<=set(labels)
    bib=set(re.findall(r'\\bibitem\{([^}]+)\}',after));assert {v.strip() for g in re.findall(r'\\cite\{([^}]+)\}',after) for v in g.split(',')}<=bib
    c=read(H/'data'/receipt);assert not c.get('isError',False) and any(json.loads(t['text']).get('kind')=='success' for t in c['content'] if t['type']=='text')
    docs[name]=dict(editor=str(p),mirror=str(R/'paper'/name),sha256=sha(p),compile_sha256=sha(H/'data'/receipt))
review=(H/'logs/review-final-documents.md').read_text(encoding='utf-8');assert all(x['sha256'] in review for x in docs.values())
save(H/'data/document-verification.json',dict(documents=docs,scope='Exact mirrors, preserved authors/settings, references, bounded independent source review and successful built-in compilation; no PDF page-by-page review.'))
previous=read(R/'milestones/224-cross-block-reconnections/data/completion.json')
for x in previous['frozen_parent_search_states'].values():assert sha(R/x['path'])==x['sha256']
git=['git','-c','core.commitGraph=false','-c','maintenance.auto=false','-c','gc.auto=0']
contributor=subprocess.check_output(git+['rev-parse','origin/research/unconditional-241'],cwd=R,text=True).strip()
completion=dict(round=225,status='PROGRESS',goal_status='ACTIVE',started_utc='2026-11-15 07:09:22 UTC',finished_utc=datetime.now(timezone.utc).isoformat(),interval=[191,233],new_q9_record=False,new_global_bound=False,complete_replacement_width=42,unresolved43=s['widths'][-1]['unresolved'],solver_exclusions_lean_certified=False,proofs=proofs,native_runs=native,connected_frontiers=read(H/'data/connected-summary.json'),model_count=538,model_archive_sha256=archive['archive_sha256'],search_summary_sha256=sha(H/'data/search-summary.json'),documents=docs,contributor_revision=contributor,independent_233_rebuild=False,frozen_parent_search_states=previous['frozen_parent_search_states'])
save(H/'data/completion.json',completion)
handoff=f'''# Current state after round 225

Goal ACTIVE. Continue construction research; coworkers handle upper bounds. The selected seed's endpoint24 route is computationally excluded for two equal-length replacements of at most42edges each. Width43 has294contexts,211inherited exclusions,58nativeINFEASIBLE and25UNKNOWN. No new snake or global bound. Read milestones/225-replacement-widths/MATHEMATICAL_NOTE.md and data/completion.json/search-summary.json.

Seed normalized bank123, endpoints0/88, append24, blockers index7/value28 and143/value56. Retain all outside indices and anchors. Target193vertices with exactlyfour bit8crossings. Widthw maximal intervals[a,a+w],a0..6, and[c,c+w],c144-w..142. Smaller windows pad into containing larger ones. Only excluded width44parents transfer; no193closure or mutual-contact premise.

Width42 initially had7UNKNOWN, IDs63–69. Their two crossing allocations(0,2)/(2,0) are both natively infeasible. combined42.json records that completion; pair42.json preserves initial outcomes. Split queries cover only those IDs and one specified allocation each, despite overbroad inherited scope wording in their raw output. Solver contradictions have no Lean certificates.

Generic direct replacement construction, interval enlargement and endpoint-crossing parity have accepted Lean receipts. Failed memory-limited attempts remain archived. Use the exact accepted dependency receipts; never relabel an interruption as PASS. Final accepted module inventory is in completion.json.

All538rawmodels remain locally; exactbytes are in solver-models.zip. Both directDFS runs are incomplete: connected43-22-zero and pruned43-22-zero. Their checkpoints preserve the remaining first/second prefixes. Context22 atwidth43 has intervals[0,43],[123,166], allocation(0,2). The original30secondrun processed1,979,706firstprefixes and15,013completefirstpaths, all failing second-root capacity. The prunedworker checks second-graph connectivity/size/colour at every firstprefix and retains20firstprefixes. Its30secondrun made249,163such prunes; no witness or exhaustion. Sourcepins differ, so keep original and prunedcheckpoints separate. All processes terminal.

Next: resume the pruned context22 allocation(0,2) from its own checkpoint under a fresh tag, or prioritize another of25open contexts. For allocation(2,0), start interval1 with --first-part1 --first-crossings0. A fixed-allocation exhaustion alone never excludes thewholecontext. Preserve all incompletefrontiers. Do not rerun unchanged width42 queries or treat the finite local barrier as global optimality.

Maintained interval191<=a(9)<=233. Contributor {contributor} is work in progress toward231, with no newcompletedboundimported. Independent233rebuild remains pending. Preserve fixed-parent222result and frozen historycases22/23/24/9 in217/211/209/209; only[1,4] exhausted among28six-coordinatechoices.

Workdir E:/Snake-in-a-box. Python C:/Users/hironakaiori/.cache/codex-runtimes/codex-primary-runtime/dependencies/python/python.exe with -B -Xutf8. Oneheavyworker, startup>=1GiB, reserve>=768MiB, private<=256MiB; threadenvall1. Lean60s -j1 -s8192. Do not restart live handles. Editor originals D:/Codex/2026-10-13/new-chat/outputs/snake9_research.tex and snake9_frontier_explanation.tex, exact mirrors paper/. Authors and hypersetup preserved; compile frontier then main. Full review last220,next230. Preserve unrelated .gitignore and milestone50 edits. Publish exact scoped manifest with Git maintenance disabled and bounded pack memory.
'''
(R/'handoff/CURRENT_STATUS.md').write_text(handoff,encoding='utf-8',newline='\n')
(R/'handoff/NEXT_AGENT_PROMPT.md').write_text('Continue the active construction goal from round225. Read CURRENT_STATUS.md and the round225 mathematical note, accepted receipts and checkpoints. Resume connected path pairs at width43; keep coworkers upper-bound work separate. Publish each productive round and preserve every incomplete state.\n',encoding='utf-8',newline='\n')
p=R/'README.md';old=p.read_text(encoding='utf-8');assert old.startswith('# Current result after round 224')
p.write_text('''# Current result after round 225

The selected endpoint-24 construction is computationally excluded for two replacement blocks of at most42edges. Width43 leaves25contexts unresolved. Crossing parity resolves the seven difficult width42cases by splitting allocations(0,2)/(2,0). The direct replacement criterion, interval enlargement and coordinate parity have accepted Lean receipts; native numerical exclusions retain their separate scope. Connected-path search now has resumable frontiers. No new snake or global bound. Goal ACTIVE.

Read [the argument](milestones/225-replacement-widths/MATHEMATICAL_NOTE.md), [evidence](milestones/225-replacement-widths/data/completion.json), [handoff](handoff/CURRENT_STATUS.md), and [short explanation](paper/snake9_frontier_explanation.tex).

## Earlier checkpoints

'''+old,encoding='utf-8',newline='\n')
print('FINALIZED_ROUND225',len(proofs),'proofmodules',len(native),'nativeruns')
