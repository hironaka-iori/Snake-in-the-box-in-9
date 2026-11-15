"""Freeze accepted evidence, manuscript receipts and an active-goal handoff."""
from pathlib import Path
from datetime import datetime,timezone
import hashlib,json,re,subprocess
H=Path(__file__).resolve().parents[1];R=H.parents[1]
D=Path('D:/Codex/2026-10-13/new-chat/outputs')
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def read(p):return json.loads(Path(p).read_bytes())
def save(p,x):Path(p).write_text(json.dumps(x,indent=2)+'\n',encoding='utf-8')
assert not (H/'data/forest-search.lock').exists()
proofs=[]
for name,count in [('FourCrossings223',1),('Endpoint223',2)]:
    p=H/'data'/(name+'-audit.json');a=read(p)
    assert a['status']=='PASS' and a['exit_code']==0 and a['stop_reason'] is None
    for pk,hk in [('source','source_sha256'),('object','olean_sha256'),('log','log_sha256')]:assert sha(a[pk])==a[hk]
    for path,digest in a['dependencies'].items():assert sha(path)==digest
    assert len(a['axioms'])==count and all(set(x['axioms'])<={'propext','Classical.choice','Quot.sound'} for x in a['axioms'])
    proofs.append(dict(module=name,receipt=str(p.relative_to(R)),sha256=sha(p),reports=count))
results=read(H/'data/search-summary.json')
for tag,row in results.items():
    assert sha(H/'data'/(tag+'.json'))==row['result_sha256']
    run=read(H/'data'/(tag+'-execution.json'))
    assert run['status']=='ACCEPTED_NATIVE_RESULT' and sha(H/'data'/(tag+'-execution.json'))==row['execution_sha256']
    assert all(sha(p)==v for p,v in run['pins'].items())
docs={}
for name,receipt in [('snake9_frontier_explanation.tex','frontier-compile-final.json'),('snake9_research.tex','main-compile-final.json')]:
    p=D/name;assert p.read_bytes()==(R/'paper'/name).read_bytes()
    before=(H/'data'/(name+'.before.txt')).read_text(encoding='utf-8');after=p.read_text(encoding='utf-8')
    assert re.search(r'\\author\{[^\n]*',before).group()==re.search(r'\\author\{[^\n]*',after).group()
    if name=='snake9_research.tex':assert re.search(r'\\hypersetup\{.*?\n\}',before,re.S).group()==re.search(r'\\hypersetup\{.*?\n\}',after,re.S).group()
    labels=re.findall(r'\\label\{([^}]+)\}',after)
    assert len(labels)==len(set(labels)) and set(re.findall(r'\\label\{([^}]+)\}',before))<=set(labels)
    assert set(re.findall(r'\\(?:ref|eqref|pageref)\{([^}]+)\}',after))<=set(labels)
    bib=set(re.findall(r'\\bibitem\{([^}]+)\}',after))
    assert {v.strip() for group in re.findall(r'\\cite\{([^}]+)\}',after) for v in group.split(',')}<=bib
    compiled=read(H/'data'/receipt)
    assert not compiled.get('isError',False) and any(json.loads(t['text']).get('kind')=='success' for t in compiled['content'] if t['type']=='text')
    docs[name]=dict(editor=str(p),mirror=str(R/'paper'/name),sha256=sha(p),compile_receipt=receipt,compile_sha256=sha(H/'data'/receipt),lines=len(after.splitlines()))
review=(H/'logs/review-final-documents.md').read_text(encoding='utf-8')
assert all(d['sha256'] in review for d in docs.values())
save(H/'data/document-verification.json',dict(scope='Exact source mirrors, preserved authors/settings, source-reference checks, bounded independent revision review and successful compiler receipts. No page-by-page visual audit.',documents=docs))
frozen=read(H.parent/'222-prefix-certificates/data/completion.json')['frozen_parent_search_states']
for row in frozen.values():assert sha(R/row['path'])==row['sha256']
contributor=subprocess.check_output(['git','-c','core.commitGraph=false','rev-parse','origin/research/unconditional-241'],cwd=R,text=True).strip()
next_step='Continue the four-crossing construction route with explicit endpoint choices and mandatory omissions. Endpoint24, retaining88, requires deletion of seed vertices28 and56 at indices7 and143. Use the resulting retained intervals as path components in a reduced reconnection model. Do not repeat unchanged d8/d12/endpoint80 timeouts or claim they exclude any path. A fresh balanced seed is an alternative. Keep both faces and crossing locations variable; do not impose a symmetry exchanging the unequal83/13 components.'
completion=dict(round=223,status='PROGRESS',goal_status='ACTIVE',utc=datetime.now(timezone.utc).isoformat(),previous_research_round=222,previous_research_result='PROGRESS',previous_interactive_turn='ROUTE_SELECTION_ONLY',interval=[191,233],new_q9_record=False,new_global_bound=False,constructor_checked=True,endpoint_exclusion_checked=True,accepted_new_modules=2,theorem_reports=3,proofs=proofs,search_results=results,native_infeasibility_lean_certified=False,contributor_revision=contributor,contributor_231_completed_or_rebuilt=False,independent_233_rebuild=False,frozen_parent_search_states=frozen,software_tests_created_or_run=False,compile_success=True,next_full_paper_review=230,next_step=next_step)
save(H/'data/completion.json',completion)
handoff=f'''# Current state after round 223

Goal ACTIVE after the user's explicit resumption. Continue constructive research only; coworkers handle upper bounds. Round223 made progress: checked five-component joining and endpoint exclusion, and executed new coupled-face queries. No new snake or global bound.

Read milestones/223-coupled-four-crossings/MATHEMATICAL_NOTE.md, data/completion.json, logs/seed-review.md and logs/model-review.md. The chosen seed is bank123/forest0, original coordinate7 normalized to bit8. Its five blocks have lengths46,83,32,13,13; face sizes94/98; endpoints0/88; ports35,195,208,232. Root0 is retained; the new endpoint must be even and lower-face. Target193 vertices, four bit8 crossings, both faces change, all ports variable. The native at-most4-omission query is INFEASIBLE in3.204s. At-most8/12 are UNKNOWN in120.063/150.031s. These are native results, no Lean infeasibility certificate. No dynamic cycle cuts were generated. Do not infer a global exclusion.

Retaining88 and ending at80 forces deletion of old port208 because both88/208 are neighbours of80. The corresponding at-most12-omission query is UNKNOWN after75s. The exact scope is in data/endpoint-scope.json; its specialized equality fixes80 despite an inherited base free-endpoint phrase. data/endpoint-cases.json records all eight lower-face neighbours and their mandatory seed omissions;89 is already in the seed and only the other seven are eligible new endpoints in this specialization. They do not cover arbitrary endpoint relocation.

FourCrossings223 and Endpoint223 passed with three public results and only standard axioms. Actual path assembly is checked under explicit pairwise premises; no new192-edge instance exists. Preserve accepted sources, objects and receipts. Independent model review and source revision review are saved. Both editor originals and exact repository mirrors compiled. Authors and hypersetup unchanged. Full-paper review last220, next230.

Maintained interval191<=a(9)<=233. Contributor revision {contributor} describes work toward231, with generated tables/certificates and final chain pending. No contributor changes merged or independently rebuilt. The233 independent rebuild remains pending and outside this construction round.

Round222 complete fixed-parent exclusion stays closed: whole saved98-edge parent and its isometry class cannot improve191 via one crossing; no92-edge partner attainment claim. Preserve frozen cases22/23/24/9 in217/211/209/209; only retained pair[1,4] exhausted among28six-coordinate choices.

Workdir E:/Snake-in-a-box. Python C:/Users/hironakaiori/.cache/codex-runtimes/codex-primary-runtime/dependencies/python/python.exe with -B -X utf8. One heavy worker, startup>=1GiB, reserve>=768MiB, private<=256MiB; native thread environment all1. Lean60s, -j1 -s8192. All round223 native/compiler jobs are terminal. Never restart a live handle after an observation timeout.

Editor sources D:/Codex/2026-10-13/new-chat/outputs/snake9_research.tex and snake9_frontier_explanation.tex; mirrors paper/. Compile frontier then main. Preserve unrelated .gitignore and milestone50 edits. Publish the exact scoped manifest; never enumerate all untracked historical files. Git flags core.commitGraph=false, maintenance.auto=false, gc.auto=0; push pack.threads=2, pack.windowMemory=64m, pack.deltaCacheSize=64m.

Next step: {next_step}
'''
for name in ['CURRENT_STATUS.md','NEXT_AGENT_PROMPT.md']:(R/'handoff'/name).write_text(handoff,encoding='utf-8',newline='\n')
header='''# Current result after round 223

The constructive route now varies both Q8 faces and all four crossings. A five-component joining constructor and the endpoint-neighbour exclusion rule passed Lean, with three public results. The neighbourhood allowing at most four omissions from the selected 191-edge seed is natively infeasible; eight/twelve omissions and an endpoint-80 specialization remain unresolved at their limits. No longer snake or new global bound. The goal remains ACTIVE; next is endpoint-directed reconnection of retained components.

Read [the mathematical explanation](milestones/223-coupled-four-crossings/MATHEMATICAL_NOTE.md), [evidence](milestones/223-coupled-four-crossings/data/completion.json), [handoff](handoff/CURRENT_STATUS.md), and [short explanation](paper/snake9_frontier_explanation.tex).

## Earlier checkpoints

'''
old=(R/'README.md').read_text(encoding='utf-8');assert not old.startswith('# Current result after round 223')
(R/'README.md').write_text(header+old,encoding='utf-8',newline='\n')
print('FROZEN_ROUND223_GOAL_ACTIVE')
