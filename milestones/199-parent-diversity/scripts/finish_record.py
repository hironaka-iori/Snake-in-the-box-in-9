from pathlib import Path
import datetime,hashlib,json,subprocess
H=Path(__file__).resolve().parents[1];R=H.parents[1]
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def read(name):return json.loads((H/'data'/(name+'.json')).read_bytes())
git=['git','-c','core.commitGraph=false','-c','maintenance.auto=false','-c','gc.auto=0']
def output(*args):return subprocess.check_output(git+list(args),cwd=R)
base='49636b49538b96ad8f437d8c6fc434d190de5b1f';head=output('rev-parse','origin/research/unconditional-241').decode().strip()
diff=output('diff',base+'..'+head,'--','milestones/33-233-lean/certify/data/replay6SB233.jsonl');(H/'logs/contributor-final.diff').write_bytes(diff)
entries=[json.loads(line[1:]) for line in diff.decode().splitlines() if line.startswith('+{')]
contributor=dict(base=base,head=head,added_replay_entries=len(entries),cases=[e['case'] for e in entries],diff_sha256=hashlib.sha256(diff).hexdigest(),scope='Contributor generation records only; no independent replay, merge or upgraded numerical bound.')
(H/'data/contributor-refresh.json').write_text(json.dumps(contributor,indent=2)+'\n',encoding='utf-8',newline='\n')
names=['all-isometries-published50','all-isometries-parents49-keep24','all-isometries-parents49-keep16','cross-parents49','mixed51-49']
censuses=[]
for name in names:
 d=read(name);assert d['status']=='COMPLETE' and d['witness'] is None
 for row in d['rows']:
  assert row['permutations']==5040 and row['isometries']==645120
  assert sum(row['intersection_histogram'].values())==645120
  assert min(int(k) for k,c in row['intersection_histogram'].items() if c)==row['minimum_intersection']
 censuses.append(dict(record=name,sha256=sha(H/'data'/(name+'.json')),rows=[{k:v for k,v in r.items() if k in ['parent','parents','permutations','isometries','minimum_intersection']} for r in d['rows']]))
searches=[]
for name in ['unrestricted50-root10','unrestricted50-root2','unrestricted50-root0','complement49']:
 d=read(name);searches.append(dict(record=name,status=d['status'],seconds=d['seconds'],arguments=d['arguments'],sha256=sha(H/'data'/(name+'.json'))))
proof=read('IsometricPlacement199-audit');assert proof['status']=='PASS' and len(proof['axioms'])==5
for p,d in proof['dependencies'].items():assert sha(p)==d,p
assert sha(proof['source'])==proof['source_sha256'] and sha(proof['object'])==proof['olean_sha256']
out=dict(round=199,status='PROGRESS',goal_status='active',utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),base_head=output('rev-parse','HEAD').decode().strip(),new_q9_record=False,new_global_bound=False,accepted_lean_modules=['IsometricPlacement199'],theorem_reports=5,numerical_censuses_lean_checked=False,censuses=censuses,solver_searches=searches,contributor=contributor,next_action='Use the minimum-overlap placements for coupled parent repairs, or improve the arbitrary-path complement search. Do not repeat complete placement scans for equivalent parent pairs. Whole-manuscript review at200.')
(H/'data/completion.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8',newline='\n')
status=f'''# Current state after round 199

Research remains active. Read milestones/199-parent-diversity/MATHEMATICAL_NOTE.md and data/completion.json. No new Q9 witness or global bound was obtained.

Symmetry has two roles. The round198 involution quotient still has three endpoint classes10,2,0. Its unrestricted50-vertex cases all remain UNKNOWN after45 seconds each, with no seed constraint. The earlier checked96-vertex paired face remains available in milestones/198-symmetry-cliques/data/paired47.json; its192-edge completion was unresolved.

For two Q7 paths with sets S,T, placing S in one Q8 face and f(T) in the other gives separated components exactly when S intersect f(T) is empty. f may be any cube isometry; no involution and no equality of parent shapes is required. This broader placement statement does not give an involution quotient. Five Lean statements in IsometricPlacement199 pass, covering path images, layer embedding, separation, representative changes and reversing pairs. Numerical censuses remain native, with no Lean replay.

Every completed relative-placement scan covers all5040 coordinate permutations and128 translations, hence645120 maps per pair. The published51-vertex parent's self-pair has minimum intersection2. All six unordered pairs from the three saved50-vertex parent classes have minimum2. Of14 published51-plus-saved49 cases,12 have minimum2 and2 have minimum3. Thus none produces the desired100-vertex paired face. Independent canonicalization of distinct parents is valid for the full isometry family, generally invalid for an involution-only scan.

The three50-vertex and fourteen49-vertex parent banks exhaust extensions of the two24-vertex prefixes of the published seed. They do not classify all Q7 paths. Two16-prefix attempts stopped at3000001 nodes each and added no new class. Save and reuse the complete placement results rather than scanning isometric copies again.

A circuit query for any49-vertex induced path in the complement of the published51-vertex parent remains UNKNOWN60 seconds. The complement has77 vertices and141 edges. This permits arbitrary second-parent shapes and has no symmetry or seed-overlap restriction. A witness would give100 paired-face vertices, still needing93 opposite-face vertices for192 edges,95 for194 or97 for196. A pair alone does not establish a Q9 lower bound.

Next: use minimum-overlap placement geometry for coupled repairs, or derive stronger complement-path restrictions before rerunning an unchanged timed-out model. Matching-step quotient paths remain another route. Whole-manuscript review is due in round200.

Contributor branch {head} added{len(entries)} replay-generation log entries. The diff is archived; no independent rebuild or merge was done. Archived235 rebuild remains pending;233/234 remain conditional.

Editor manuscripts are D:/Codex/2026-10-13/new-chat/outputs/snake9_research.tex and snake9_frontier_explanation.tex, mirrored in E:/Snake-in-a-box/paper. Preserve authors and hypersetup, plus unrelated .gitignore and milestone50 modifications. Keep one heavy worker,1GiB startup memory,768MiB reserve,256MiB per Lean process and60-second Lean checks. Research is active.
'''
for name in ['CURRENT_STATUS.md','NEXT_AGENT_PROMPT.md']:(R/'handoff'/name).write_text(status,encoding='utf-8',newline='\n')
brief='''# Round 199: symmetry placements beyond involutions

The general separation criterion for two paths in opposite faces needs any cube isometry, without an involution or congruent parent shapes. Five statements supporting the construction and symmetry reductions pass Lean.

Full scans of645120 isometries per saved parent pair rule out100-vertex faces in the three-class50-plus50 bank and fourteen51-plus49 cases. These finite native exclusions do not cover all Q7 paths. Three unrestricted quotient endpoint searches and an arbitrary-path complement query remain UNKNOWN. No new Q9 witness or global bound is claimed.

Read [the argument](MATHEMATICAL_NOTE.md), [completion record](data/completion.json), [Lean source](lean/IsometricPlacement199.lean), and [handoff](../../handoff/CURRENT_STATUS.md). Input hashes, intersection histograms, proof receipt and raw solver outcomes are saved. The solver models are packaged in data/solver-models.zip. Research remains active.
'''
(H/'README.md').write_text(brief,encoding='utf-8',newline='\n')
p=R/'README.md';s=p.read_text(encoding='utf-8');assert not s.startswith('# Current result after round 199')
prefix='''# Current result after round 199

Symmetry placement now includes all cube isometries and different parent shapes. Complete finite scans exclude100-vertex paired faces from the saved50-plus50 and51-plus49 parent banks. The general placement reasoning passes Lean; the numerical censuses remain native. The broader complement-path search is unresolved, and no new Q9 record or global bound is claimed.

Read [round199](milestones/199-parent-diversity/README.md), [the argument](milestones/199-parent-diversity/MATHEMATICAL_NOTE.md), [verification status](milestones/199-parent-diversity/data/completion.json), [handoff](handoff/CURRENT_STATUS.md), and [frontier explanation](paper/snake9_frontier_explanation.tex). Research remains active.

## Earlier checkpoints

'''
p.write_text(prefix+s,encoding='utf-8',newline='\n')
print('SAVED_ROUND199',len(censuses),'censuses;',len(searches),'solver outcomes;5 Lean reports')
