from pathlib import Path
import hashlib,json,re,datetime
R=Path('E:/Snake-in-a-box');H=R/'milestones/189-middle-replacements';P=R/'milestones/188-dimensional-constructions';D=Path('D:/Codex/2026-10-13/new-chat');W=D/'work';O=D/'outputs'
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
four=json.loads((H/'data/exact-edits4.json').read_text());assert four['status'] in ['INFEASIBLE','UNKNOWN']
minimum=5 if four['status']=='INFEASIBLE' else 4
three_text=r'''A further search requires a 97-edge path with the same endpoints
to retain exactly 93 of the original 96 vertices. All other cube vertices
are available, and no external nine-dimensional restriction is imposed.
The solver reports infeasibility in 28.641 seconds. Combined with the
smaller complete enumerations, this gives the computational conclusion
that at least four original vertices must be omitted. This last step
depends on the solver exclusion, which has no Lean contradiction
certificate.
'''
if minimum==5:
    four_text=r'''The corresponding search retaining exactly 92 original vertices
also reports infeasibility. Under these solver results, a fixed-endpoint
97-edge replacement must omit at least five original vertices and add
at least seven new vertices. The numerical restriction is specific to
this path and retains the stated certificate limitation.
'''
    next_action='Search a97-edge replacement with exactly five original vertices omitted, or vary the crossing ports and neighbouring components. The cases with up to four omissions are computationally excluded, with the three/four cases lacking Lean contradiction certificates.'
else:
    four_text=r'''The corresponding four-vertex omission search remains unresolved
after 90 seconds. Thus the present computational lower bound is four
omitted original vertices and six added vertices. No exclusion is claimed
for the four-vertex case.
'''
    next_action='The exact-four-omission case is UNKNOWN after90seconds. Seek a different search formulation or branch on the changed vertices, or vary crossing ports and neighbouring components. Do not repeat the unchanged90second query.'
for name in ['round189_section.tex','round189_short.tex']:
    p=W/name;s=p.read_text();assert '% ROUND189_THREE_CHANGE_RESULT' in s;s=s.replace('% ROUND189_THREE_CHANGE_RESULT',three_text+'\n'+four_text);p.write_text(s,encoding='utf-8',newline='\n')
p=O/'snake9_research.tex';s=p.read_text(encoding='utf-8');original=s;marker='\\section{Construction experiments and their scope}\\label{app:experiments}'
assert 'sec:middle-replacements' not in s and s.count(marker)==1
s=s.replace(marker,(W/'round189_section.tex').read_text()+'\n'+marker)
s=s.replace('The next construction step is to vary the middle path together with','The construction problem permits varying the middle path together with')
s=s.replace('The associated 194-edge target remains a construction hypothesis.','The associated 194-edge target remains a construction hypothesis.\nFixed-component searches and replacement enumerations identify\nrestrictions in this family without producing a longer snake.')
for pattern in [r'\\author\{[^\n]+',r'\\hypersetup\{.*?\n\}']:assert re.search(pattern,s,re.S).group()==re.search(pattern,original,re.S).group()
p.write_text(s,encoding='utf-8',newline='\n')
p=O/'snake9_frontier_explanation.tex';s=p.read_text(encoding='utf-8');s=s.replace('Research state after round 188','Research state after round 189')
s=s.replace('The next step\nis the fixed-endpoint 95-to-97 replacement search, followed by varying\nthe surrounding components if that restricted problem is excluded.','The restrictions obtained from this replacement investigation are\ndescribed below.')
s=s.replace('\\textbf{7. What is proved, and what remains.}',(W/'round189_short.tex').read_text()+'\n\\textbf{7. What is proved, and what remains.}')
s=s.replace('Round 188 adds the construction comparison and exact joining deduction.','Round 189 adds replacement restrictions within the common construction\nfamily and a checked overlap-repair inequality.').replace('research records 175--188','research records 175--189');p.write_text(s,encoding='utf-8',newline='\n')
for n in ['snake9_research.tex','snake9_frontier_explanation.tex']:(R/'paper'/n).write_bytes((O/n).read_bytes())
order=json.loads((H/'data/current-order.json').read_text());accepted=[];pins={}
for n in order:
    p=H/'data'/(n+'-audit.json');a=json.loads(p.read_text());assert a['status']=='PASS' and a['exit_code']==0 and a['stop_reason'] is None
    assert sha(a['source'])==a['source_sha256'] and sha(a['object'])==a['olean_sha256'] and sha(a['log'])==a['log_sha256']
    for q,h in a['dependencies'].items():
        if q in pins:assert pins[q]==h
        pins[q]=h
    accepted.append({'module':n,'receipt_sha256':sha(p),'dependency_reports':len(a['axioms'])})
for q,h in pins.items():assert sha(q)==h,q
completion={'round':189,'status':'PROGRESS','goal_status':'active','utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'previous_turn':'PROGRESS: published round188 joining theorem, witness analysis and construction direction.','accepted_modules':accepted,'native_complete_contiguous_sizes':list(range(1,43)),'native_complete_intervals_through42':3087,'native_partial_contiguous_size43_complete_intervals':23,'native_two_nonadjacent_removed_position_pairs':4278,'three_omissions_solver':'INFEASIBLE','four_omissions_solver':four['status'],'computational_minimum_original_vertices_omitted_for97':minimum,'qualification':'The numerical exclusions are native computations; the three/four-omission solver exclusions and nested49 exclusions have no Lean contradiction certificates. No global bound follows.','next_action':next_action,'new_record':False,'new_global_bound':False,'full_manuscript_review':'pending','contributors_fetched':'f393c48e5e583e57d3cbb66e4330f960033229b1','bank_sha256':sha(R/'work/bank9.json')}
(H/'data/completion.json').write_text(json.dumps(completion,indent=2)+'\n')
note=f'''# Round189: restrictions on replacing the common95-edge component

The goal remains active. The user requested relations6→7,7→8,8→9; this round follows the95→97 replacement target from round188. No longer snake or improved global upper bound was found.

## Mathematical content

The observed family47,95,191 has48,96,192 selected vertices. The relations95=31+47+15+2 and191=95+94+2 balance the selected vertices across both faces. This is an observed family, not a universal doubling construction.

The exact joining rule gives31+49+15+2=97 and, with compatible outer paths totalling94, gives193. NestedReplacement189 checks these conditional implications. The existence of the49/97 paths with the required compatibility is unproved.

The overlap-repair inequality is |A∩B|≤|A\\A'|+|B\\B'| whenever A',B' are disjoint. Omit designated crossing ports from the ground set. Each original overlap must be removed from at least one set. ReplacementBudget189 checks the counting proof, including the fixed-outer case. It does not check the entire placement enumeration.

## Finite evidence

1. All84contexts for the common95 type leave162 allowed Q8 vertices. Leaf pruning and the block-cut route remove none. The first fixed-port97 search is UNKNOWN at120.062seconds. Context canonicalization concerns the original path together with its allowed set, not the bare allowed graph with ports.
2. Nested47→49 replacement leaves64–72 allowed Q7vertices. In context0 it is INFEASIBLE in1.593seconds. Removing all externalQ9restrictions leaves82 vertices and is INFEASIBLE in114.375seconds. This excludes changing only the47 piece while retaining the31/15 pieces and ports; it is not a globalQ8 orQ9 result. The nested allowed sets were independently reproduced after a read-only model review.
3. All1440 endpoint-preserving placements of the applicable97-edge truncation of the displayed98-edge snake have≥23 forbidden overlaps across all84contexts. Minima distribution23:7,24:33,25:36,26:8. All960 placements of the49-edge truncations of the displayed50-edge snake have≥11 overlaps; distribution11:34,12:30,13:17,14:3. These classify only the stated seed placements. The general repair inequality implies corresponding minimum total removals before compatibility can hold.
4. Contiguous local replacement: all3087 intervals of1–42 internal vertices are exhausted with no97-edge replacement, even without externalQ9constraints. Size43 has23 completed intervals and a partial next interval; the120second run ended incomplete. No universal size43 exclusion. The unchanged path outside the interval retains its order. This is not a lower bound of43 omitted vertices.
5. Two separated changes: all4278 pairs of nonadjacent internal positions, both orientations of the retained middle chain, and every connector-length pair(2,4),(3,3),(4,2) are enumerated. No replacement exists in this finite search. Three retained chains force this decomposition: the endpoint chains are fixed, the middle can reverse, and the two connectors must total six edges. Their endpoints were nonconsecutive in the original induced path, so neither connector can have length one. Adjacent and single changes were covered by contiguous sizes1/2. Keeping every original vertex cannot lengthen a fixed-endpoint induced path because its original edges are forced.
6. A generalQ8 circuit model retaining exactly93/96 original vertices reports INFEASIBLE in28.641seconds. It includes all outside cube vertices and does not impose anyQ9outer restrictions. The exact-four-omission model reports {four['status']} in{four['seconds']:.3f}seconds. Thus the current computational minimum is{minimum} omissions and{minimum+2} additions for a97-edge fixed-port replacement. The solver exclusions have no Lean contradiction certificates.

## Search-model argument

Binary vertex variables choose the path. Each physical cube edge between two selected vertices must be used as a directed circuit arc in one direction. A mandatory virtual arc from the terminal port to the initial port closes the desired path. Self-loops mark unselected vertices. The single-circuit constraint excludes disconnected cycles; the forced physical arcs exclude chords. Ports have Hamming distance3 (or5 in the nested problem), so the virtual arc is not a physical cube edge. Every returned feasible path would be decoded and checked pairwise. No feasible longer path was returned.

The native depth-first enumeration forbids every new interior vertex that meets a retained vertex other than its connection endpoints, and excludes chords to earlier new vertices and premature adjacency to the terminal endpoint. It considers all remaining cube neighbours. Distance pruning is a necessary condition only. Its complete ranges and partial stopping point are recorded separately.

## Next action

{next_action}

Consider changes spread across several components: retaining the31/15 pieces already blocks the nested improvement, and every single interval through size42 is excluded. The evidence does not exclude a97-edge path with the same ports after larger coordinated changes, a different port pair, or different surrounding paths. The194 target remains provisional and196 remains unresolved.

## Verification and preservation

Four local modules have accepted receipts: two reused joining-support modules and two new modules for overlap repair and nested conditional construction. All source, object, log and dependency hashes were rechecked. Standard Lean axioms only; no admitted proof. These checks do not establish the finite solver exclusions. The pending round188 directQ8 pairwise recheck is preserved unchanged. No proof or search worker remains active at closure.

Round187 upper-bound state is preserved:93/98 clause batches, conditional233/234, and archived235 awaiting complete independent rebuild. No contribution branch was merged. The fetched contributor head remainsf393c48e. The manuscript-wide review remains pending. ExistingD: manuscripts andE: mirrors preserve authors and hypersetup.
'''
(H/'MATHEMATICAL_NOTE.md').write_text(note,encoding='utf-8',newline='\n')
(H/'README.md').write_text(f'''# Round189: middle-path replacement restrictions

The 95→97 construction investigation found no longer snake. It excludes the nested47→49 replacement with31/15 pieces fixed in the native solver, every contiguous replacement through42 internal vertices by exhaustive enumeration, and all changes at up to two internal positions. The exactly-three-omission solver case is INFEASIBLE; exactly four is {four['status']}.

The computational minimum is{minimum} original vertices omitted and{minimum+2} added for a fixed-endpoint97-edge replacement. Solver exclusions have no Lean contradiction certificates. The general overlap-repair inequality and nested joining implications pass Lean.

Read [the argument](MATHEMATICAL_NOTE.md), [completion](data/completion.json), [local enumeration](data/local-repair-17-48.json), [two-position enumeration](data/two-changes.json), and [current handoff](../../handoff/CURRENT_STATUS.md). The goal remains active. {next_action}
''',encoding='utf-8',newline='\n')
handoff=f'''# Current frontier after round189

The goal is active. Continue the dimension-lifting construction direction requested by the user. Previous round188 was progress; this round adds actual replacement exclusions and new checked deductions.

Read milestones/189-middle-replacements/MATHEMATICAL_NOTE.md and data/completion.json. {next_action}

The common family47,95,191 doubles selected-vertex counts48,96,192. Generic three-path joining is checked. The nested31+49+15+2=97 implication and subsequent193 implication pass Lean under explicit compatibility. Existence is not proved.

Exact finite scope: full fixed-outer95→97 search UNKNOWN at120seconds; nested47→49 with31/15 fixed INFEASIBLE even after externalQ9restrictions are removed (82allowed vertices). All contiguous blocks through42 are excluded; size43only23intervals complete. All two-position changes including reversal of the middle retained chain are excluded by direct enumeration. Exactly3 omissions is solver-INFEASIBLE; exactly4 is {four['status']}. Computational minimum{minimum} omissions/{minimum+2} additions. No Lean contradiction certificates for solver exclusions, and no complete Lean interpretation of the native enumeration.

Known-seed alternatives:1440 placements of the applicable97-edge truncation have≥23 forbidden overlaps;960 placements of49-edge truncations have≥11. The generic overlap-removal counting inequality passes Lean. These classifications concern only the displayed seed families. No new record or global upper bound.

All queries are terminal. Preserve their models, outputs and scope; do not restart because of missing updates. One research worker at a time. Lean guard remains1GiB free at startup,768MiB reserve,256MiB private memory. Round188 directQ8 witness recheck remains pending; its native check and Lean transition/cut counts passed.

Upper-bound checkpoint unchanged: round18793/98clause batches (11904/12424), critical floor15 and actual-snake transfer pending; conditional233 uses4716m+5L≤1103475; paid-key census426 (373afterfloor15) lacks fullLeancoverage. Retained234 and archived235 carry their existing qualifications. The full manuscript-wide review is overdue and pending.

Fetched research/unconditional-241 atf393c48e5e583e57d3cbb66e4330f960033229b1; not merged or independently rebuilt. Preserve unrelated.gitignore and milestones/50-three-count-return/excess-screen/data/critical-family.json edits. Author order and hypersetup remain unchanged in the existingD: manuscripts andE: mirrors.
'''
(R/'handoff/CURRENT_STATUS.md').write_text(handoff,encoding='utf-8',newline='\n');(R/'handoff/NEXT_AGENT_PROMPT.md').write_text('Continue from the active round189 construction frontier.\n\n'+handoff,encoding='utf-8',newline='\n')
p=R/'README.md';p.write_text(f'''# Current result after round189

The common95-edge middle path resists local improvement: all single replacement intervals through42 internal vertices and all two-position changes are excluded by native enumeration. The exactly-three-omission solver case is INFEASIBLE; exactly four is {four['status']}. The nested47→49 replacement is also excluded with its31/15pieces fixed. These are restricted computational results without complete Lean certificates, and no longer snake or global bound follows.

The overlap-repair inequality and nested joining implications pass Lean. Read [round189](milestones/189-middle-replacements/README.md), [the argument](milestones/189-middle-replacements/MATHEMATICAL_NOTE.md), [handoff](handoff/CURRENT_STATUS.md), [paper](paper/snake9_research.tex), and [frontier explanation](paper/snake9_frontier_explanation.tex). The goal remains active.

## Earlier checkpoints

'''+p.read_text(),encoding='utf-8',newline='\n')
(H/'scripts/publication.py').write_text((P/'scripts/publication.py').read_text().replace('Round188','Round189'),encoding='utf-8',newline='\n');(H/'scripts/close.py').write_bytes(Path(__file__).read_bytes())
print(json.dumps({'accepted_modules':len(accepted),'four_omissions':four['status'],'computational_minimum_omissions':minimum,'manuscripts':[sha(O/n) for n in ['snake9_research.tex','snake9_frontier_explanation.tex']]},indent=2))
