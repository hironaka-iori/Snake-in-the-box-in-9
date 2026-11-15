"""Freeze research evidence and an active construction handoff."""
from pathlib import Path
from datetime import datetime,timezone
import hashlib,json,re,subprocess
H=Path(__file__).resolve().parents[1];R=H.parents[1];D=Path('D:/Codex/2026-10-13/new-chat/outputs')
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def read(p):return json.loads(Path(p).read_bytes())
def save(p,x):Path(p).write_text(json.dumps(x,indent=2)+'\n',encoding='utf-8',newline='\n')
assert not (H/'data/forest-search.lock').exists()
summary=read(H/'data/search-summary.json');assert summary['short_family_excluded'] and len(summary['unresolved44'])==92
for tag,row in summary['runs'].items():
    assert sha(H/'data'/(tag+'.json'))==row['result_sha256']
    run=read(H/'data'/(tag+'-execution.json'));assert run['status']=='ACCEPTED_NATIVE_RESULT' and run['stop_reason'] is None
    assert sha(H/'data'/(tag+'-execution.json'))==row['execution_sha256']
    assert all(sha(p)==v for p,v in run['pins'].items())
proofs=[]
for name in ['TwoBlocks224','TwoBlockEscape224']:
    p=H/'data'/(name+'-audit.json');a=read(p)
    assert a['status']=='PASS' and a['exit_code']==0 and a['stop_reason'] is None
    for pk,hk in [('source','source_sha256'),('object','olean_sha256'),('log','log_sha256')]:assert sha(a[pk])==a[hk]
    assert all(sha(p)==v for p,v in a['dependencies'].items())
    assert len(a['axioms'])==1 and set(a['axioms'][0]['axioms'])<={'propext','Classical.choice','Quot.sound'}
    proofs.append(dict(module=name,receipt=str(p.relative_to(R)),sha256=sha(p),reports=1))
archive=read(H/'data/model-archive.json');assert len(archive['files'])==316 and sha(H/'data'/archive['archive'])==archive['archive_sha256']
assert all(sha(H/'data'/name)==row['sha256'] for name,row in archive['files'].items())
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
    docs[name]=dict(editor=str(p),mirror=str(R/'paper'/name),sha256=sha(p),compile_receipt=receipt,compile_sha256=sha(H/'data'/receipt),lines=len(after.splitlines()))
review=(H/'logs/review-final-documents.md').read_text(encoding='utf-8');assert all(row['sha256'] in review for row in docs.values())
save(H/'data/document-verification.json',dict(documents=docs,scope='Exact mirrors, preserved authors/settings and labels, bounded independent source review, successful compiler receipts. No page-by-page visual audit.'))
frozen=read(H.parent/'223-coupled-four-crossings/data/completion.json')['frozen_parent_search_states'];assert all(sha(R/row['path'])==row['sha256'] for row in frozen.values())
git=['git','-c','core.commitGraph=false','-c','maintenance.auto=false','-c','gc.auto=0']
def gitout(*args):return subprocess.check_output(git+list(args),cwd=R,text=True).strip()
contributor=gitout('rev-parse','origin/research/unconditional-241')
save(H/'data/github-final.json',dict(main=gitout('rev-parse','origin/main'),contributor=contributor,opening_contributor='4b6b73907af9d76d7a8f3ca592a13dc89c8ad21d',observation='Further231 stageB/C work-in-progress snapshots. No merge or independent rebuild; no new completed bound asserted.'))
next_step='Continue the endpoint24 two-region construction. Prepare width34 maximal contexts first, using combined crossing counts and correct odd vertex parity counts. In particular [130,164] contains both old crossing edges130/163, so never reuse width33 fixed0/1 allocation. Locate the smallest unresolved width in34–43. For its open contexts, enumerate actual connected replacement paths and solve the other path in the remaining compatible graph; retain incomplete enumeration states. Do not repeat unchanged44 degree/flow timeouts. The33-edge family is closed by the contact-free native calculation; no general192-edge exclusion is claimed.'
completion=dict(round=224,status='PROGRESS',previous_goal_turn='PROGRESS',goal_status='ACTIVE',started_utc='2026-11-15 06:48:55 UTC',finished_utc=datetime.now(timezone.utc).isoformat(),interval=[191,233],new_q9_record=False,new_global_bound=False,accepted_new_modules=2,theorem_reports=2,proofs=proofs,short_contexts=224,short_static=171,short_native_infeasible=53,short_unresolved=0,short_numerical_exclusion_requires_bank_closure=False,long_contexts=301,long_static=107,long_native_infeasible=102,long_unresolved=92,flow_retries=16,flow_all_unknown=True,biconnected_new_exclusions=0,solver_infeasibility_lean_certified=False,model_archive_sha256=archive['archive_sha256'],search_summary_sha256=sha(H/'data/search-summary.json'),contributor_revision=contributor,independent_233_rebuild=False,frozen_parent_search_states=frozen,software_tests_created_or_run=False,compile_success=True,next_full_paper_review=230,next_step=next_step)
save(H/'data/completion.json',completion)
handoff=f'''# Current state after round 224

Goal ACTIVE. Continue constructive research only; coworkers handle upper bounds. Round224 is PROGRESS: actual intermediate-path construction and conditional two-block interaction theorem passed Lean, and a new two-short-block construction family was completely excluded natively. No longer snake or global bound.

Read milestones/224-cross-block-reconnections/MATHEMATICAL_NOTE.md and data/completion.json/search-summary.json. Generic theorem: an escape from a family closed under individual short replacements must have new/old cross-contact in both directions. Contact includes equality; use old positional interiors, not globally omitted sets. Bank application uses native193 closure through33, never44. TwoBlocks224 and TwoBlockEscape224 passed, two public results; the latter's failed first source/log are preserved separately.

Seed remains normalized bank123, endpoint0 retained, old endpoint88 retained, append24. Required omitted original positions are7/value28 and143/value56. Two equal-length replacement blocks preserve all outside indices and all anchors; target193 vertices, exactlyfour bit8crossings. For width33, maximal contexts are [a,a+33] for a0..6 and[c,c+33] for c111..142,224 total. The firstreplacement has0crossings, second1. Contact-free final run excludes171 geometrically and53 by nativeINFEASIBLE; zero unresolved. The finite exclusion does NOT depend on bank closure. Native solver contradictions have no Lean replay.

Width44 has301 maximal contexts,107 geometric exclusions,102 nativeINFEASIBLE,92 unresolved. The combined44.json table contains all301distinctIDs. Biconnected reduction of92open domains removedzero vertices and rejectedzero cases; no unchangedrerun. Flow strengthening of16selected cases leftall16UNKNOWN, so92remainopen. Do not count COMPLETE_COVERAGE as completeexclusion. Per-query models/results are frozen.

All316 rawpbtxt models remain locally in data/; their exactbytes arepublished in solver-models.zip with model-archive.json hashes. Extract thearchive into data/ to reproduce paths. Four native runs and all Lean processes areterminal. No softwaretests werecreated orrun. Independent mathematical input/model reviews and finalsource review arein logs/.

Maintained interval191<=a(9)<=233. Contributor {contributor} has furtherwork-in-progress toward231; no newboundmerged/rebuilt. Independent233 rebuildremains pending andoutside thisconstructive round. Preserve round222 fixed-parent one-crossing exclusion and frozen parent-history cases22/23/24/9 in217/211/209/209. Only[1,4] exhaustedamong28six-coordinatechoices.

Workdir E:/Snake-in-a-box. Python C:/Users/hironakaiori/.cache/codex-runtimes/codex-primary-runtime/dependencies/python/python.exe with -B -X utf8. Oneheavyworker, startup>=1GiB, reserve>=768MiB, private<=256MiB; native threadenv all1. Lean60s -j1 -s8192. Neverrestart a livehandle after observationtimeout.

Editor originals D:/Codex/2026-10-13/new-chat/outputs/snake9_research.tex and snake9_frontier_explanation.tex; exact mirrors paper/. Authors/hypersetup preserved; both compiled. Compilefrontier thenmain. Fullpaperreviewlast220,next230. Preserveunrelated.gitignore and milestone50 edits. Publish exactscopedmanifest; currenthelper intentionally publishesmodelzip instead ofrawpbtxt. Gitflags core.commitGraph=false maintenance.auto=false gc.auto=0; push pack.threads=2 pack.windowMemory=64m pack.deltaCacheSize=64m.

Next step: {next_step}
'''
for name in ['CURRENT_STATUS.md','NEXT_AGENT_PROMPT.md']:(R/'handoff'/name).write_text(handoff,encoding='utf-8',newline='\n')
header='''# Current result after round 224

A checked interaction theorem explains why simultaneous replacements must interfere to escape a family closed under separate changes. The endpoint-24 construction using two blocks of at most 33 edges is computationally excluded across all 224 maximal contexts, without relying on that closure premise. At 44 edges, 209 of 301 contexts are excluded and 92 remain unresolved. No longer snake or new global bound. Goal ACTIVE; next is the smallest unresolved two-region width and explicit compatible replacement paths.

Read [the argument](milestones/224-cross-block-reconnections/MATHEMATICAL_NOTE.md), [evidence](milestones/224-cross-block-reconnections/data/completion.json), [handoff](handoff/CURRENT_STATUS.md), and [short explanation](paper/snake9_frontier_explanation.tex).

## Earlier checkpoints

'''
old=(R/'README.md').read_text(encoding='utf-8');assert not old.startswith('# Current result after round 224');(R/'README.md').write_text(header+old,encoding='utf-8',newline='\n')
print('FROZEN_ROUND224_GOAL_ACTIVE')
