"""Freeze the construction frontier and keep the research goal active."""
from pathlib import Path
from datetime import datetime,timezone
import hashlib,json,re,subprocess
H=Path(__file__).resolve().parents[1];R=H.parents[1];D=Path('D:/Codex/2026-10-13/new-chat/outputs')
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def read(p):return json.loads(Path(p).read_bytes())
def save(p,j):Path(p).write_text(json.dumps(j,indent=2)+'\n',encoding='utf-8',newline='\n')
s=read(H/'data/search-summary.json');free=read(H/'data/free-summary.json');coverage=read(H/'data/coverage46.json')
assert s['complete_through']==46 and not s['width46_unresolved']
assert sha(H/'data/coverage46.json')==s['coverage_sha256']
for j in [coverage,free]:assert all(sha(p)==h for p,h in j['pins'].items())
assert not list((H/'data').glob('*.lock'))
native=[]
for run in s['runs']+free['runs']:
    tag=run['tag'];ep=H/'data'/(tag+'-execution.json');e=read(ep)
    rp=H/'data'/tag/'result.json' if tag.startswith('reduced') else H/'data'/(tag+'.json')
    assert e['status']=='ACCEPTED_NATIVE_RESULT' and e['exit_code']==0 and e['stop_reason'] is None
    assert all(sha(p)==h for p,h in e['pins'].items()) and sha(rp)==e['result_sha256']
    assert sha(ep)==run['receipt_sha256'] and sha(rp)==run['result_sha256'];native.append(run)
preparations=[]
for tag,name in [('lower-preparation','lower-pairs.json'),('boundary-preparation','boundary-lower-pairs.json')]:
    p=H/'data'/(tag+'-execution.json');e=read(p)
    assert e['status']=='ACCEPTED_NATIVE_RESULT' and e['exit_code']==0 and e['stop_reason'] is None
    assert all(sha(q)==h for q,h in e['pins'].items()) and sha(H/'data'/name)==e['result_sha256']
    preparations.append(dict(tag=tag,receipt_sha256=sha(p)))
proofs=[]
for name,expected in [('ProjectionPorts229',3),('CrossingAllocation229',2)]:
    p=H/'data'/(name+'-audit.json');a=read(p)
    assert a['status']=='PASS' and a['exit_code']==0 and a['stop_reason'] is None
    for pk,hk in [('source','source_sha256'),('object','olean_sha256'),('log','log_sha256')]:assert sha(a[pk])==a[hk]
    assert all(sha(q)==h for q,h in a['dependencies'].items())
    assert len(a['axioms'])==expected and all(set(r['axioms'])<={'propext','Classical.choice','Quot.sound'} for r in a['axioms'])
    proofs.append(dict(module=name,reports=expected,receipt_sha256=sha(p)))
archive=read(H/'data/model-archive.json');assert len(archive['files'])>=945
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
save(H/'data/document-verification.json',dict(documents=docs,scope='Exact mirrors, preserved authors/settings, references, independent bounded source review and built-in compilation. No page-by-page PDF review.'))
previous=read(R/'milestones/228-wider-replacement-constructions/data/completion.json')
for r in previous['frozen_parent_search_states'].values():assert sha(R/r['path'])==r['sha256']
git=['git','-c','core.commitGraph=false','-c','maintenance.auto=false','-c','gc.auto=0']
contributor=subprocess.check_output(git+['rev-parse','origin/research/unconditional-241'],cwd=R,text=True).strip()
completion=dict(round=229,status='PROGRESS',previous_round_status=previous['status'],goal_status='ACTIVE',started_utc='2026-11-15 14:32:06 UTC',finished_utc=datetime.now(timezone.utc).isoformat(),interval=[191,233],new_q9_record=False,new_global_bound=False,complete_four_crossing_width=46,four_crossing_contexts=315,variable_crossing_status=free['status'],variable_crossing_counts=free['counts'],variable_crossing_unresolved=free['unresolved'],proofs=proofs,native_runs=native,preparations=preparations,model_count=len(archive['files']),model_archive_sha256=archive['archive_sha256'],coverage46_sha256=sha(H/'data/coverage46.json'),free_summary_sha256=sha(H/'data/free-summary.json'),documents=docs,contributor_revision=contributor,independent_233_rebuild=False,solver_exclusions_lean_certified=False,frozen_parent_search_states=previous['frozen_parent_search_states'])
targets=read(H/'data/two-crossing-frontier.json')
assert all(sha(p)==h for p,h in targets['pins'].items())
assert [r['context'] for r in targets['contexts']]==free['unresolved']
completion['complete_six_crossing_width']=46 if not free['six_unresolved_after_free'] else None
completion['two_crossing_frontier_sha256']=sha(H/'data/two-crossing-frontier.json')
save(H/'data/completion.json',completion)
remaining=len(free['unresolved']);newly=sum(r['statuses'].get('INFEASIBLE',0) for r in free['runs'] if r['tag'].startswith('counts46'))
handoff=f'''# Current state after round 229

Goal ACTIVE. Round 229 is PROGRESS: complete native four-crossing exclusion through width 46, general projection/compatibility and crossing-allocation lemmas checked in Lean, and a broader construction search with no prescribed crossing count. Read milestones/229-two-layer-construction/MATHEMATICAL_NOTE.md and data/completion.json. No new snake or global bound.

Workdir E:/Snake-in-a-box. The family uses normalized bank123, endpoints0/88, appends24 after88, retains outside positions and block anchors, and replaces two intervals by equal-length paths. Width46 maximal intervals [a,a+46], a=0..6, and [c,c+46], c=98..142. There are315 contexts. Padding covers shorter blocks. Seed, endpoint, number of blocks, retained positions and length preservation remain restrictions even when crossing count is free.

Four-crossing cover:106 static +89 empty upper-template contexts +96 reduced contexts +24 direct contexts =315. The185 reducible contexts have allocations(0,1):20,(0,2):13,(1,1):100,(1,2):52. 3535 original configurations,7070 boundary branches,5866 fixed-neighbour rejections,318 disconnections,886 survivors,538 groups,496 representatives. Representative790 is contained in prior228 representative593;495 new reduced queries plus24 direct queries are infeasible. Eight reduced timeouts were closed by longer retries. The boundary cut here depends on the complete native45 FOUR-crossing cover. Do not apply it to wider widths or other crossing counts without the matching premise. data/coverage46.json is the complete literal cover.

Broader frontier: the six-crossing batch returned200 INFEASIBLE and9 UNKNOWN among209 nonstatic contexts. It used no boundary cut. The first unrestricted-crossing batch returned77 INFEASIBLE and132 UNKNOWN. A stronger unrestricted model forbids totalfour using the complete same-context four-crossing cover and forbids totalsix only in the original200 completed six-crossing contexts. It adds no crossing cap or boundary restriction. Its132 targeted queries and a longer retry of the31 remaining unknowns excluded {newly} more in total. Combined unrestricted status is {free['status']}: {315-remaining} excluded contexts, {remaining} unresolved. Exact IDs and intervals are in data/free-summary.json; unresolved IDs: {free['unresolved']}. Preserve every UNKNOWN as unresolved. Six-crossing unknowns resolved by the larger cover, if any, are recorded separately without mutating the original batch or creating circular premises.

ProjectionPorts229 has3 accepted reports: the general own-port/other-upper filter, its equivalence to indexed single-crossing compatibility for actual induced paths, and exclusion of a positive-length lower path's nonjoining anchor from upper projections. CrossingAllocation229 has2 reports: desired upper-anchor count is a lower bound under parity and nonzero-two premises, and equal total forces equality separately. The latter is general arithmetic rather than a new literal table. All sources are pinned; LayerJoining is a verified reused dependency. Extraction of ports and graph premises, domain preparation, enumeration, coverage assembly and solver contradictions remain native. No end-to-end Lean certificate is claimed.

The round228 generic mask issue is corrected in229: only actual upper-prefix/suffix joining ports are exempt from own upper projections. Do not modify older pinned sources. The general theorem does not validate an arbitrary supplied port list; intended endpoint equalities and path injectivity remain required. All current lower segments have positive length. The entire193vertex pairwise inducedness audit is retained for every prospective witness.

All nine originally unknown six-crossing cases are now excluded by the broader queries, so the same family is completely excluded at six crossings as well. This is acyclic: those nine received no six-count cut. Do not rerun them. The current count worker remains pinned to the original200 six exclusions and must not be silently altered.

Next prioritize the EXACT-TWO construction within the eleven unrestricted cases. data/two-crossing-frontier.json records a necessary allocation calculation only, with no new search: IDs34,38,39,40 have zero replacement crossings in both blocks; IDs79,83,84,124,126,128,129 have one crossing in the first block and zero in the second. These are single-lower-segment cases again and can use upper-piece enumeration with actual-port masks. Do not impose any boundary-change cut from the four/six covers. Prepare the new two-crossing domains/tasks in a new milestone, deduplicate and compare with existing genuinely matching exclusions, then search. The remaining family also permits counts of at least8; no claim that a candidate must have2 is made. Inspect forced anchor edges and exact task equality for repeated descriptions before expensive queries.

A possible additional necessary inequality is suggested by an interior visit to a face: it needs at least three selected vertices, since a zero-edge visit repeats a vertex and a one-edge visit creates a chord after the two vertical joins. If c is a replacement's crossing count, r its number of upper anchors and u/l its selected upper/lower vertex counts, this suggests 2u+r>=3c and 2l+(2-r)>=3c, with c=0 handled separately. This deduction is NOT implemented or Lean checked in round229. Prove the run-count argument before adding it, and inspect old results for an existing version. Alternatively improve connectivity/cycle reasoning or change endpoint/seed if this family stalls. Partial greedy growth remains parked; do not repeat unchanged one-ended growth of the excluded112vertexprefixes. First target192 edges;196 remains conjectural. Coworkers handle global upper bounds.

All current child processes are terminal; no live search is carried into the handoff. Raw exported models remain local and in solver-models.zip. Do not rerun closed four-crossing tasks or unchanged completed unrestricted queries. Later runs may use larger limits or justified stronger constraints for unresolved IDs only.

Maintained interval191<=a(9)<=233; independent233 rebuild remains pending. Contributor revision {contributor} was fetched; commit summaries were inspected without importing or rebuilding its Lean4.35 port or a new global bound. Preserve fixed-parent222 and frozen history cases22/23/24/9 in217/211/209/209; only[1,4] exhausted among28six-coordinatechoices.

One heavy worker at a time; startup>=1GiB free, reserve>=768MiB, private<=256MiB. Native thread variables all1; Lean60s,-j1,-s8192. Python C:/Users/hironakaiori/.cache/codex-runtimes/codex-primary-runtime/dependencies/python/python.exe with -B -X utf8. Poll existing live handles; do not restart on observation failure. Editor originals D:/Codex/2026-10-13/new-chat/outputs/snake9_research.tex and snake9_frontier_explanation.tex; exact mirrors paper/. Preserve all three authors and hypersetup. Compile frontier then main. Full main review last220, next230. Preserve unrelated .gitignore and milestone50 edits; use exact scoped publication, Git maintenance off and bounded pack memory.
'''
(R/'handoff/CURRENT_STATUS.md').write_text(handoff,encoding='utf-8',newline='\n')
(R/'handoff/NEXT_AGENT_PROMPT.md').write_text('Goal ACTIVE. Read CURRENT_STATUS.md and round229 evidence. Four- and six-crossing width46 families are completely excluded; unrestricted crossing count leaves11cases. Prioritize exacttwo in data/two-crossing-frontier.json: four(0,0) replacement allocations and seven(1,0), permitting single-lower-segment reduction again. No two-crossing search or boundary cut is already available. Counts>=8 remain possible. Do not rerun closed queries. Full manuscript review is due in round230. Preserve historical frontiers, authors and hyperlink settings.\n',encoding='utf-8',newline='\n')
p=R/'README.md';old=p.read_text(encoding='utf-8');assert old.startswith('# Current result after round 228')
p.write_text(f'''# Current result after round 229

The fixed endpoint-24 two-block construction is computationally excluded through width46 when the final snake has four coordinate-8 crossings. All315 maximal contexts are covered. General projection compatibility and crossing-allocation implications passed Lean. A broader search removes the prescribed crossing count: {315-remaining} contexts are excluded and {remaining} remain unresolved. These are native construction-family exclusions, with no new snake or global bound. The goal remains active.

Read [the argument](milestones/229-two-layer-construction/MATHEMATICAL_NOTE.md), [four-crossing cover](milestones/229-two-layer-construction/data/coverage46.json), [variable-crossing frontier](milestones/229-two-layer-construction/data/free-summary.json), [evidence](milestones/229-two-layer-construction/data/completion.json), [handoff](handoff/CURRENT_STATUS.md), and [short explanation](paper/snake9_frontier_explanation.tex).

## Earlier checkpoints

'''+old,encoding='utf-8',newline='\n')
print('FINALIZED_ROUND229',remaining,'variable-crossing cases unresolved; goal ACTIVE')
