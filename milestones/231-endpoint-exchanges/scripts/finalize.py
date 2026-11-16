from pathlib import Path
from datetime import datetime,timezone
import hashlib,json,re,subprocess
H=Path(__file__).resolve().parents[1];R=H.parents[1];D=Path('D:/Codex/2026-10-13/new-chat/outputs')
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def read(p):return json.loads(Path(p).read_bytes())
def save(p,x):Path(p).write_text(json.dumps(x,indent=2)+'\n',encoding='utf-8',newline='\n')
s=read(H/'data/colour-survey.json');q=read(H/'data/hamilton.json')
assert s['status']=='COMPLETE_SURVEY' and len(s['cases'])==23127 and len(s['duplicates'])==73
assert q['status']=='COMPLETE_QUERY_BATCH' and len(q['results'])==49 and all(x['status']=='INFEASIBLE' for x in q['results'])
assert {x['id'] for x in q['results']}=={x['id'] for x in s['survivors']}
assert not list((H/'data').glob('*.lock'))
native=[]
for tag in ['colour-survey','hamilton']:
    ep=H/'data'/(tag+'-execution.json');e=read(ep)
    assert e['status']=='ACCEPTED_NATIVE_RESULT' and e['exit_code']==0 and e['stop_reason'] is None
    assert all(sha(p)==h for p,h in e['pins'].items()) and sha(H/'data'/(tag+'.json'))==e['result_sha256']
    native.append(dict(tag=tag,receipt_sha256=sha(ep),result_sha256=e['result_sha256']))
a=read(H/'data/ColourContraction231-audit.json');assert a['status']=='PASS' and len(a['axioms'])==4
for pk,hk in [('source','source_sha256'),('object','olean_sha256'),('log','log_sha256')]:assert sha(a[pk])==a[hk]
assert all(sha(p)==h for p,h in a['dependencies'].items())
assert all(set(x['axioms'])<={'propext','Classical.choice','Quot.sound'} for x in a['axioms'])
archive=read(H/'data/model-archive.json');assert len(archive['files'])==49
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
    bib=set(re.findall(r'\\bibitem\{([^}]+)\}',after));assert {v.strip() for g in re.findall(r'\\cite\{([^}]+)\}',after) for v in g.split(',')}<=bib
    c=read(H/'data'/receipt);assert not c.get('isError',False) and any(json.loads(t['text']).get('kind')=='success' for t in c['content'] if t['type']=='text')
    docs[name]=dict(editor=str(p),mirror=str(R/'paper'/name),sha256=sha(p),compile_sha256=sha(H/'data'/receipt))
review=(H/'logs/review-final-documents.md').read_text(encoding='utf-8')
assert all(x['sha256'] in review for x in docs.values()) and sha(H/'MATHEMATICAL_NOTE.md') in review
previous=read(R/'milestones/230-two-crossing-frontier/data/completion.json')
for x in previous['frozen_parent_search_states'].values():assert sha(R/x['path'])==x['sha256']
git=['git','-c','core.commitGraph=false','-c','maintenance.auto=false','-c','gc.auto=0']
contributor=subprocess.check_output(git+['rev-parse','origin/research/unconditional-241'],cwd=R,text=True).strip()
completion=dict(round=231,status='PROGRESS',goal_status='ACTIVE',pause_after_round=233,started_utc='2026-11-16 13:37:19 UTC',finished_utc=datetime.now(timezone.utc).isoformat(),interval=[191,233],new_q9_record=False,new_global_bound=False,majority_class_exclusion_complete=True,minority_class_case='OPEN',seed_count=131,distinct_bases=145,distinct_majority_sets=23127,native_runs=native,proof_reports=4,proof_receipt_sha256=sha(H/'data/ColourContraction231-audit.json'),separator_certificates=45,remaining_solver_only_cases=[21881,22201,22514,22834],solver_exclusions_lean_certified=False,documents=docs,contributor_revision=contributor,contributor_231_completed=False,independent_233_rebuild=False,full_manuscript_review_round=230,next_full_manuscript_review_round=240,frozen_parent_search_states=previous['frozen_parent_search_states'])
save(H/'data/completion.json',completion)
save(H/'data/document-verification.json',dict(documents=docs,scope='Preserved authors, hypersetup and labels; exact mirrors; bounded source review and successful built-in compilation. No full PDF visual review.'))
handoff=f'''# Current state after round 231

Goal ACTIVE. The user requests pause after round 233. Round 231 is PROGRESS; two rounds remain before the pause. Work in E:/Snake-in-a-box. Read milestones/231-endpoint-exchanges/MATHEMATICAL_NOTE.md and data/completion.json.

Construction route: contract one chosen parity class U. An opposite-parity vertex with exactly two neighbours in U labels an edge between them. Hamiltonian paths in this graph correspond to induced paths with majority class U and both endpoints there, of length 2|U|-2. Parallel labels can be collapsed. No old order, crossing count, endpoints or opposite-colour selection is fixed. ColourContraction231 has four accepted Lean reports: actual constructor, converse adjacency, extracted injectivity/disjointness and same-parity nonadjacency. Cube colour extraction, finite graphs and native contradictions remain separate.

Complete survey: 131 checked seeds yield 145 distinct labelled 96-vertex parity classes. The 160 possible additions per base yield 23,200 descriptions, 23,127 distinct 97-sets and 73 exact duplicates. Initial exclusions: 17,271 isolated vertices and 5,807 excess leaves. All 49 surviving mandatory-dummy circuit queries are INFEASIBLE. Forty-five also have independently inspected elementary separator certificates. Cases 21881,22201,22514,22834 retain native solver evidence. No witness or new global bound.

Scope: this excludes 192-edge snakes whose 97-vertex MAJORITY class contains an entire saved 96-vertex class. Fixing the 96-vertex MINORITY class remains open. Round 232 should examine it: opposite vertices with two selected neighbours are internal edge labels; vertices with one neighbour are possible endpoint labels. Seek a Hamiltonian path on the 96 fixed vertices whose two ends admit distinct endpoint labels. Labels at different ends are automatically distinct because each has a singleton neighbour set. Do not apply the majority-only exclusion to this case. If it also closes, an improvement must change both seed colour classes; this is currently conditional.

The round-230 two-block family through width 46 is closed for all crossing counts. Do not rerun it. The fixed-parent round-222 ceiling and all frozen coordinate-history states remain intact. Partial greedy growth is reserved for a suitable later subproblem. Coworkers handle global upper bounds.

Maintained interval: 191<=a(9)<=233; independent full rebuild of 233 pending. Contributor revision {contributor} has a 231-target chain with plain/H8, share, contextual-refutation and floor premises. The bounded review found no completed unconditional 231 final assembly/audit. Keep 233 as the maintained upper bound; read logs/contributor-review.md. No contributor work was imported or compiled.

All research workers are terminal. The 49 raw models remain local and in data/solver-models.zip. Both manuscripts compiled; originals remain in D:/Codex/2026-10-13/new-chat/outputs/, with exact paper/ mirrors. Preserve Iori Hironaka, Tommy Ma, Steven Zhan and complete hypersetup. Last full source review was round 230, next 240. Preserve unrelated .gitignore and milestone-50 edits. Use one heavy worker/compiler, startup>=1GiB, reserve>=768MiB, private<=256MiB, native threads1, Lean60s/-j1/-s8192. Use saved guards and narrow publication with Git maintenance off and bounded pack memory.
'''
for name in ['CURRENT_STATUS.md','NEXT_AGENT_PROMPT.md']:(R/'handoff'/name).write_text(handoff,encoding='utf-8',newline='\n')
old=(R/'README.md').read_text(encoding='utf-8')
(R/'README.md').write_text('''# Current result after round 231

Parity-class contraction gives an exact Hamiltonian-path construction criterion. All 23,127 distinct 97-vertex majority classes obtained by enlarging one saved seed class are computationally excluded. Forty-five of the final 49 graphs also have elementary separator explanations. Four general constructor/converse statements passed Lean. The fixed-minority-class case remains open; the global interval remains 191--233. The goal is active, with a user-requested pause after round 233.

Read [the argument](milestones/231-endpoint-exchanges/MATHEMATICAL_NOTE.md), [evidence](milestones/231-endpoint-exchanges/data/completion.json), [handoff](handoff/CURRENT_STATUS.md), and [short explanation](paper/snake9_frontier_explanation.tex).

## Earlier checkpoints

'''+old,encoding='utf-8',newline='\n')
print('FINALIZED_ROUND231; ACTIVE; PAUSE_AFTER233')
