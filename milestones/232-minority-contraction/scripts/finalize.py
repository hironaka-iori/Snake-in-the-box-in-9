from pathlib import Path
from datetime import datetime,timezone
import hashlib,json,re,subprocess
H=Path(__file__).resolve().parents[1];R=H.parents[1];D=Path('D:/Codex/2026-10-13/new-chat/outputs')
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def read(p):return json.loads(Path(p).read_bytes())
def save(p,x):Path(p).write_text(json.dumps(x,indent=2)+'\n',encoding='utf-8',newline='\n')
q=read(H/'data/minority.json');assert q['status']=='COMPLETE_QUERY_BATCH' and len(q['results'])==145
assert q['statuses']=={'FEWER_THAN_TWO_PORTS':2,'INFEASIBLE':81,'UNSUPPORTED_LEAF':62}
assert not list((H/'data').glob('*.lock'))
ep=H/'data/minority-execution.json';e=read(ep)
assert e['status']=='ACCEPTED_NATIVE_RESULT' and e['exit_code']==0 and e['stop_reason'] is None
assert all(sha(p)==h for p,h in e['pins'].items()) and sha(H/'data/minority.json')==e['result_sha256']
native=[dict(tag='minority',receipt_sha256=sha(ep),result_sha256=e['result_sha256'])]
proofs=[]
for module,count in [('MinorityContraction232',4),('FixedColour232',3)]:
    a=read(H/'data'/(module+'-audit.json'));assert a['status']=='PASS' and len(a['axioms'])==count
    for pk,hk in [('source','source_sha256'),('object','olean_sha256'),('log','log_sha256')]:assert sha(a[pk])==a[hk]
    assert all(sha(p)==h for p,h in a['dependencies'].items())
    assert all(set(x['axioms'])<={'propext','Classical.choice','Quot.sound'} for x in a['axioms'])
    proofs.append(dict(module=module,reports=count,receipt_sha256=sha(H/'data'/(module+'-audit.json'))))
archive=read(H/'data/model-archive.json');assert len(archive['files'])==81
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
previous=read(R/'milestones/231-endpoint-exchanges/data/completion.json')
for x in previous['frozen_parent_search_states'].values():assert sha(R/x['path'])==x['sha256']
git=['git','-c','core.commitGraph=false','-c','maintenance.auto=false','-c','gc.auto=0']
contributor=subprocess.check_output(git+['rev-parse','origin/research/unconditional-241'],cwd=R,text=True).strip()
completion=dict(round=232,status='PROGRESS',goal_status='ACTIVE',pause_after_round=233,started_utc='2026-11-16 13:50:20 UTC',finished_utc=datetime.now(timezone.utc).isoformat(),interval=[191,233],new_q9_record=False,new_global_bound=False,minority_class_exclusion_complete=True,both_colour_changes_required=True,fixed_colour_optimum=191,seed_count=131,distinct_bases=145,native_runs=native,proofs=proofs,separator_certificates=33,remaining_solver_only_count=48,solver_exclusions_lean_certified=False,documents=docs,contributor_revision=contributor,contributor_231_completed=False,independent_233_rebuild=False,full_manuscript_review_round=230,next_full_manuscript_review_round=240,frozen_parent_search_states=previous['frozen_parent_search_states'])
save(H/'data/completion.json',completion)
save(H/'data/document-verification.json',dict(documents=docs,scope='Preserved authors, hypersetup and labels; exact mirrors; bounded source review and successful built-in compilation. No full PDF visual review.'))
handoff=f'''# Current state after round 232

Goal ACTIVE. Pause after round 233 as requested; one round remains. Round 232 is PROGRESS. Work in E:/Snake-in-a-box. Read milestones/232-minority-contraction/MATHEMATICAL_NOTE.md and data/completion.json.

Round 231 excluded every 97-vertex majority class obtained by adding a vertex to a saved 96-set: 145 bases, 23,127 distinct enlarged sets and 49 final native exclusions. Round 232 fixes those 145 classes as the minority class instead. Opposite vertices with exactly two selected neighbours label internal edges; singleton-neighbour vertices label possible endpoints. A Hamiltonian path on U must end at two distinct eligible ports. Its internal labels and two endpoint labels give 192 edges. The other colour class, endpoints and order remain free.

Complete cover: two bases lack two ports, 62 have unsupported graph leaves, and 81 native mandatory-dummy circuit queries are INFEASIBLE. Thirty-three augmented graphs have elementary separators: 20 singletons and 13 pairs leave more components than removed vertices. The other 48 retain native solver evidence. Independent review reconstructed all 145 cases and 81 models. MinorityContraction232 has four accepted reports; FixedColour232 adds three colour-count and length reports. Actual cube extraction and finite certificates retain their native or written scope.

Combined, any 192-edge snake must omit at least one vertex of each parity from every saved seed, including cube-isometric copies by inverse-automorphism transport. A retained entire 96-set would be its minority class or contained in its majority class, both excluded. Keeping one chosen class exactly fixed has maximum 191: alternation gives length at most 192, that top case is excluded, and the old seed attains 191. This uses native finite premises and gives no global bound.

Round 233 target: change a fixed minority class by one vertex, allowing its opposite class to vary freely. Enumerate distinct 95-vertex cores from the 145 bases, then insert a same-parity vertex. Only its nine neighbours change roles: zero to one selected neighbour gives an endpoint label; one to two gives an internal label; two to three makes the label unusable. Reuse the constructor and whole-path validation. Treat exact duplicates carefully. Complete coverage requires every core/addition description and every remaining Hamiltonian query to be resolved. Preserve the precise frontier if limits interrupt the search. This family has not yet been searched.

Maintained interval: 191<=a(9)<=233; independent full rebuild of 233 pending. Contributor {contributor} adds no newly inspected completed 231 assembly; the latest update concerns scheduling. Preserve the closed round-230 two-block family, round-222 fixed-parent ceiling and frozen history frontiers. Coworkers handle upper bounds. Partial greedy growth remains a later option.

All workers are terminal. The 81 raw models remain local and archived in data/solver-models.zip. Both original TeX files in D:/Codex/2026-10-13/new-chat/outputs/ match paper/ and compiled. Preserve all authors and hypersetup. Full source review: last round 230, next 240. Preserve unrelated .gitignore and milestone-50 edits. Use one heavy worker or compiler, startup 1 GiB, reserve 768 MiB, private memory 256 MiB, native threads 1; Lean 60s/-j1/-s8192. Use narrowly scoped publication and bounded Git memory. Pause after 233.
'''
for name in ['CURRENT_STATUS.md','NEXT_AGENT_PROMPT.md']:(R/'handoff'/name).write_text(handoff,encoding='utf-8',newline='\n')
old=(R/'README.md').read_text(encoding='utf-8')
(R/'README.md').write_text('''# Current result after round 232

All 145 saved minority classes are computationally excluded for 192 edges, complementing the majority-class cover. A 192-edge snake must change both parity classes relative to every saved seed or cube-isometric copy. Keeping one complete 96-vertex class fixed has exact restricted maximum 191. Seven new general Lean reports support the construction and counting arguments; finite graphs and contradictions retain their stated native scope. The global interval remains 191--233. Goal active; pause after round 233.

Read [the argument](milestones/232-minority-contraction/MATHEMATICAL_NOTE.md), [evidence](milestones/232-minority-contraction/data/completion.json), [handoff](handoff/CURRENT_STATUS.md), and [short explanation](paper/snake9_frontier_explanation.tex).

## Earlier checkpoints

'''+old,encoding='utf-8',newline='\n')
print('FINALIZED_ROUND232; ACTIVE; PAUSE_AFTER233')
