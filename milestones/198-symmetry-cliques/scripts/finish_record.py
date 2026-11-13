from pathlib import Path
import datetime,hashlib,json
H=Path(__file__).resolve().parents[1];R=H.parents[1]
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
proofs=[]
for p in sorted((H/'data').glob('*-audit.json')):
 d=json.loads(p.read_bytes());assert d['status']=='PASS'
 proofs.append(dict(module=d['module'],reports=len(d['axioms']),receipt_sha256=sha(p)))
accepted={d['module'] for d in proofs};pending=sorted(p.stem for p in (H/'lean').glob('*.lean') if p.stem not in accepted)
searches=[]
for name in ['circuit50-omit5','newpair-complete192']:
 d=json.loads((H/'data'/(name+'.json')).read_bytes());searches.append(dict(record=name,status=d['status'],seconds=d['seconds'],arguments=d['arguments']))
ordered=[]
for n in [38,26,18,12]:
 d=json.loads((H/f'data/ordered50-keep{n}.json').read_bytes())
 ordered.append(dict(keep=n,rows=[dict(status=r['status'],nodes=r['nodes'],seconds=r['seconds'],best_vertices=len(r['best'])) for r in d['rows']]))
contributor=json.loads((H/'data/contributor-refresh.json').read_bytes())
out=dict(round=198,status='PROGRESS',previous_turn_classification='PROGRESS: round197 classified affine symmetry placements and published checked quotient identities.',goal_status='active',utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),base_head='7574279f2a16d2272c1940b2a7d8876b005cbafc',accepted_modules=proofs,pending_modules=pending,endpoint_reduction_checked='EndpointTransport198' in accepted,pair_checked=all(f'PairRows198_{i}' in accepted for i in range(4)),triangle_noncontainment_checked='Cliques198' in accepted,cliques=8,triangles=32,endpoint_representatives=[10,2,0],endpoint_class_sizes=[32,64,32],paired_forest_vertices=96,paired_path_edges=47,comparison_forests=36,cross_distance_histogram=[0,0,160,390,576,658,388,104,28],ordered_searches=ordered,solver_searches=searches,contributor=contributor,new_q9_record=False,new_global_bound=False,next_action='Use the three endpoint representatives in unrestricted50-vertex quotient searches, or search the no-matching subfamily separately. The new47-edge pair remains an unresolved candidate for a192-edge four-port completion. Diversifying near-optimal Q7 parent paths is also available; cube-isometric copies of the same parent do not diversify the placement census.')
(H/'data/completion.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8',newline='\n')
status=f'''# Current state after round 198

The goal remains active. Read milestones/198-symmetry-cliques/MATHEMATICAL_NOTE.md and data/completion.json. No new Q9 record or global numerical bound was obtained.

For row4147 of round197, the quotient is Q7 plus h, where h swaps(1,4),(3,6) and translates by126. The Q8 extension has minimum partner distance three. The quotient has eight disjoint K4s and32 triangles. Each clique contributes at most two path vertices. Coordinate0 is a product factor; its paired-clique crossing restriction is already implied by square cuts.

There are exactly three endpoint classes, of sizes32,64,32 with representatives10,2,0. They are distances0,1,2 from the triangle vertices. Paired translations, fixed-coordinate translations and pair exchange act transitively in each class. Thus three unrestricted fixed-endpoint cases cover every50-vertex quotient path. This reduction is invalid with an untransported fixed-seed constraint. The subgroup used also preserves ordinary Q7 edges, so the no-matching subfamily can use the same representatives.

Connected prefix regrowth gives a48-vertex quotient path using no matching steps and hence two47-edge Q8 paths. Their cross-distance histogram is[0,0,160,390,576,658,388,104,28], different from all 36 face forests saved in round195. This proves inequivalence to that comparison set, not to every face of every known Q9 snake. The witness is data/paired47.json. The first path starts63, ends1, and has transitions42104260210430240530421043024056042153124012310. The partner starts137 and ends255.

The18-vertex retained-prefix extension maxima are exactly46 and48 quotient vertices in the two orientations (447558 and31252 search nodes). The12-prefix searches stopped at35 seconds each; no upper conclusion follows. The connected circuit query for50 vertices and at most5 seed omissions is UNKNOWN90.047s. The new96-vertex paired face needs97 opposite-face vertices for192 edges; its four-port completion is UNKNOWN120.047s. All are restricted computations, not Lean contradiction certificates. Do not rerun unchanged timed-out models.

Accepted Lean modules: {len(proofs)}; theorem reports: {sum(p['reports'] for p in proofs)}. Endpoint transport checked: {out['endpoint_reduction_checked']}. Complete concrete pair checked: {out['pair_checked']}. Concrete triangle noncontainment checked: {out['triangle_noncontainment_checked']}. Pending sources: {', '.join(pending) if pending else 'none'}. The generic endpoint reduction retains the full finite quotient and no seed premise. The exact three-orbit classification also has the written distance and transitivity argument.

An initial large endpoint-data proof exceeded256MiB; it was split into128-edge blocks. Startup refusals, interrupted compilation, failed source and plan snapshots are preserved. Use scripts/resume_proofs.py only for unfinished modules and scripts/check_core.py for an individual pinned check. Accepted artifacts remain immutable. All worker handles must be terminal before publication.

Next construction work: three unrestricted endpoint cases, or the simpler no-matching family S intersect h(S)=empty. Ordinary cube parity balance is valid only in the latter family. A50-vertex quotient path would give a100-vertex paired face, still requiring93 opposite vertices for192 edges or95 for194. Consider different near-optimal Q7 parent paths when a fixed parent stagnates; isometric copies of one parent are already covered by the symmetry placement census. Exhausting the three endpoint cases would restrict this symmetry, not establish a global Q9 upper bound.

Contributor branch {contributor['head']} reports2998/3127 certificates built. Its diff and progress report are archived; it was neither merged nor independently rebuilt. Archived235 rebuild remains pending;233/234 remain conditional. Whole-manuscript review next at200.

Editor manuscripts remain D:/Codex/2026-10-13/new-chat/outputs/snake9_research.tex and snake9_frontier_explanation.tex, mirrored in E:/Snake-in-a-box/paper. Preserve authors, hypersetup and unrelated .gitignore and milestone50 edits. Keep one heavy worker,1GiB startup free memory,768MiB reserve,256MiB Lean process limit and60-second proof checks. Research remains active.
'''
for name in ['CURRENT_STATUS.md','NEXT_AGENT_PROMPT.md']:(R/'handoff'/name).write_text(status,encoding='utf-8',newline='\n')
brief=f'''# Round 198: clique restrictions and endpoint classes

The chosen quotient has eight K4 groups,32 triangles and exactly three endpoint classes, represented by10,2,0. This reduces unrestricted path searches to three endpoint cases; a retained seed must be transported as well.

A connected extension search gives two separated 47-edge Q8 paths. Their cross-distance histogram differs from all 36 saved comparison forests. Their 192-edge opposite-face completion remains unresolved after120.047 seconds. No longer Q9 snake or new numerical bound is claimed.

Read [the argument](MATHEMATICAL_NOTE.md), [completion record](data/completion.json), [concrete pair](data/paired47.json), and [handoff](../../handoff/CURRENT_STATUS.md). Accepted Lean modules: {len(proofs)}, theorem reports: {sum(p['reports'] for p in proofs)}. Endpoint reduction checked: {out['endpoint_reduction_checked']}; complete pair checked: {out['pair_checked']}; triangle noncontainment checked: {out['triangle_noncontainment_checked']}. The completion record lists any pending sources separately. Finite search outcomes have no Lean contradiction certificates.

The exact initial solver models are packaged in data/solver-models.zip. The connected circuit and flow models require no later cycle cuts. Resource refusals and failed proof attempts are retained. Research remains active.
'''
(H/'README.md').write_text(brief,encoding='utf-8',newline='\n')
p=R/'README.md';s=p.read_text(encoding='utf-8');assert not s.startswith('# Current result after round 198')
prefix='''# Current result after round 198

The symmetry quotient now has a three-case endpoint reduction and eight clique restrictions. Connected regrowth supplies two separated 47-edge Q8 paths, inequivalent to the 36 saved comparison forests. Their 192-edge completion remains unresolved. No new Q9 record or global numerical bound is claimed.

Read [round198](milestones/198-symmetry-cliques/README.md), [the argument](milestones/198-symmetry-cliques/MATHEMATICAL_NOTE.md), [verification status](milestones/198-symmetry-cliques/data/completion.json), [handoff](handoff/CURRENT_STATUS.md), and [frontier explanation](paper/snake9_frontier_explanation.tex). Research remains active.

## Earlier checkpoints

'''
p.write_text(prefix+s,encoding='utf-8',newline='\n')
print('SAVED',len(proofs),'accepted modules;',len(pending),'pending')
