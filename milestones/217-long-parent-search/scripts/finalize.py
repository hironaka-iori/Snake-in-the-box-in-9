"""Save the completed continuation, evidence limits and direct-construction handoff."""
from pathlib import Path
from datetime import datetime, timezone
import hashlib, json, re

H = Path(__file__).resolve().parents[1]
R = H.parents[1]
P = H.parent / '216-joint-word-support'
D = Path('D:/Codex/2026-10-13/new-chat/outputs')
def sha(p): return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def write(p, s): p.write_text(s.strip() + '\n', encoding='utf-8', newline='\n')
def save(p, x): write(p, json.dumps(x, indent=2))
def read(p): return json.loads(p.read_bytes())

assert not (H / 'data/history-search.lock').exists()
s = read(H / 'data/search-summary.json')
assert s['status'] == 'OPEN'
assert sha(H / 'data/case-22/state.json') == s['state_sha256']
transfer = read(H / 'data/frontier-transfer.json')
assert transfer['engine_changed'] is False
for path, digest in transfer['reused_evidence'].items(): assert sha(path) == digest
proofs = []
for name, count in [('TwoStep216', 5), ('Joint216', 3), ('PathJoint216', 1), ('LiteralJoint216', 2)]:
    p = P / 'data' / (name + '-audit.json'); d = read(p)
    assert d['status'] == 'PASS' and d['exit_code'] == 0 and d['stop_reason'] is None
    for pk, hk in [('source','source_sha256'), ('object','olean_sha256'), ('log','log_sha256')]: assert sha(d[pk]) == d[hk]
    for path, digest in d['dependencies'].items(): assert sha(path) == digest
    assert len(d['axioms']) == count
    assert all(set(a['axioms']) <= {'propext','Classical.choice','Quot.sound'} for a in d['axioms'])
    proofs.append({'module':name, 'receipt':str(p.relative_to(R)), 'sha256':sha(p), 'reports':count})
docs = {}
for name, receipt in [('snake9_frontier_explanation.tex','frontier-compile.json'), ('snake9_research.tex','main-compile.json')]:
    p = D / name
    assert p.read_bytes() == (R / 'paper' / name).read_bytes()
    before = (H / 'data' / ('before-' + name)).read_text(encoding='utf-8')
    after = p.read_text(encoding='utf-8')
    assert re.search(r'\\author\{[^\n]*', before).group() == re.search(r'\\author\{[^\n]*', after).group()
    if name == 'snake9_research.tex':
        assert re.search(r'\\hypersetup\{.*?\n\}', before, re.S).group() == re.search(r'\\hypersetup\{.*?\n\}', after, re.S).group()
    labels = re.findall(r'\\label\{([^}]+)\}', after)
    assert len(labels) == len(set(labels))
    assert set(re.findall(r'\\(?:ref|eqref|pageref)\{([^}]+)\}', after)) <= set(labels)
    bib = set(re.findall(r'\\bibitem\{([^}]+)\}', after))
    assert {v.strip() for g in re.findall(r'\\cite\{([^}]+)\}', after) for v in g.split(',')} <= bib
    result = read(H / 'data' / receipt)
    assert not result.get('isError', False)
    assert any(json.loads(c['text']).get('kind') == 'success' for c in result['content'] if c['type'] == 'text')
    docs[name] = {'editor':str(p), 'mirror':str(R / 'paper' / name), 'sha256':sha(p), 'compile_receipt':'data/' + receipt, 'compile_sha256':sha(H / 'data' / receipt)}
save(H / 'data/document-verification.json', {'scope':'Exact mirrors, preserved authors/settings, references and saved compilation success; no page-by-page visual audit.', 'documents':docs})
chain = read(H / 'data/chain-audit.json')
assert chain['status'] == 'PASS_SAVED_TRANSFER_AND_NEW_TRANSITIONS'
assert chain['final']['sha256'] == s['state_sha256'] and chain['new_jobs'] == s['new_jobs']
assert chain['cumulative'] == {k:s[k] for k in ['jobs','nodes','seconds']}
frozen = {}
for case, folder, jobs, pending, nodes in [('22','216-joint-word-support',400,9,2044830), ('23','211-subset-capacity',296,11,3721372), ('24','209-slice-capacity',150,8,9625900), ('9','209-slice-capacity',150,3,8142891)]:
    p = H.parent / folder / 'data' / ('case-' + case) / 'state.json'; d = read(p)
    assert d['status'] == 'OPEN' and d['committed_jobs'] == jobs and len(d['frontier']) == pending and d['nodes'] == nodes
    frozen[case] = {'path':str(p.relative_to(R)), 'sha256':sha(p), 'state_jobs':jobs, 'pending':pending, 'state_nodes':nodes, 'counter_scope':d.get('counter_scope','historical cumulative')}
intent = read(H / 'data/round-intent.json')
graphs = read(H / 'data/complement-graph.json')
assert sha(R / graphs['source']) == graphs['sha256']
next_step = ('Prioritize the direct 93-edge partner of the saved 98-edge Q8 parent at both endpoints 0 and 78. '
             'Use exactly the 158 allowed vertices, one prescribed endpoint and the other endpoint free. '
             'Adapt the selected-degree and cycle-cut approach from rounds190/192, removing every replacement-specific overlap, omission and crossing constraint. '
             'Select 94 vertices with47 of each parity; exactly two endpoint indicators, each bounded by its selection indicator; conditional selected-degree=2-endpoint. '
             'Use valid square/six-cycle cuts and add disconnected-cycle cuts as needed. '
             'A connected witness gives 192 Q9 edges through the existing Lean-checked joining theorem. '
             'Inspect and Lean-check any new witness; UNKNOWN or a resource stop gives no exclusion. '
             'Do not repeat the already excluded fixed-parent 97 query or assume this alternative is faster.')
completion = {'round':217, 'status':'PROGRESS', 'previous_goal_turn':'PROGRESS', 'started_utc':intent['started_utc'],
    'utc':datetime.now(timezone.utc).isoformat(), 'goal_state':'ACTIVE', 'pause_policy':intent['pause_policy'],
    'email_sent':False, 'email_limitation':'No sending connector available.', 'interval':[191,233],
    'contributor_revision':intent['contributor_at_start'], 'contributor_changed':False, 'independent_233_rebuild':False,
    'new_q9_record':False, 'new_global_bound':False, 'new_six_coordinate_exclusions':0,
    'accepted_new_modules':0, 'reused_proofs':proofs, 'native_engine_changed':False,
    'search':s, 'frozen_other_states':frozen, 'six_coordinate_unresolved':27,
    'chain_audit_sha256':sha(H / 'data/chain-audit.json'),
    'review_hashes':{name:sha(H / 'logs' / name) for name in ['long-chain-review.md','compatible-parent-review.md']},
    'graph_analysis_sha256':sha(H / 'data/complement-graph.json'), 'ledger_version':2, 'counter_scope':'milestone-local',
    'complete_native_certificate':False, 'complete_normalization_certificate':False,
    'software_tests_created_or_run':False, 'compile_success':True, 'document_verification':'data/document-verification.json', 'next_step':next_step}
save(H / 'data/completion.json', completion)
note = f'''# Round 217: continuation and a direct compatible-path target

The longer-job hypothesis remains unconfirmed as a performance claim. The unchanged engine accepts {s['new_jobs']} local jobs, with outcomes {s['new_statuses']}, examines {s['local_nodes']:,} new nodes and reports {s['local_seconds']:.3f} solver seconds. Case 22 retained [0,6] remains OPEN with {s['pending']} regions. No different parent, longer snake, or complete coordinate-case exclusion was obtained.

The final cumulative totals are {s['jobs']} jobs, {s['nodes']:,} nodes and {s['seconds']:.3f} solver seconds. State SHA-256: {s['state_sha256']}. Version2 state counters are local to 217. The pinned predecessor summary supplies 1140 jobs,6,496,107 nodes and658.343 seconds. The 216 state itself contains only its 400 local jobs. The audit checks this distinction, the 400 predecessor receipts against their manifest, nine transferred regions, unchanged engine/model pins, each new transition and cumulative arithmetic. This is an audit of saved records; native execution and complete normalization are not kernel-certified.

## More direct construction target

Let P be the saved 98-edge Q8 path and let t be endpoint 0 or 78. Remove only V(P) excluding t. The remaining induced graph has 158 vertices. An induced 93-edge path beginning at t, with its other endpoint free, intersects P only at t. Place the two paths in opposite Q9 faces and join at t. Their length is $98+93+1=192$. Inside each face, inducedness is inherited. Across faces, adjacency requires equal projected vertices, so the single overlap creates exactly the joining edge. The existing LayerJoining/IntegerLayerBridge result already checks this implication; this round adds no Lean theorem.

Source inspection confirms that the old 97-edge partner queries allowed arbitrary partner shapes and returned INFEASIBLE for both endpoints. These are solver exclusions without Lean contradiction certificates. Both old 93-edge queries returned UNKNOWN after about 30 seconds. A different optimal parent may be needed for the 196-edge one-crossing construction, subject to those exclusions; it is unnecessary as a preliminary stage for the unresolved 192 target. The prior frontier wording implying that every construction route needs a different parent has been corrected.

The graph enumeration records 337 edges and 79 vertices of each parity at either endpoint. Both graphs are connected and have no articulation vertex or pair of equal open neighbourhoods. Their degree histograms differ, so these two allowed graphs are not isomorphic and cannot be treated as one endpoint case. This is consistent with the previously Lean-checked obstruction to reversing the saved parent; it is no new global symmetry claim. For roots 0/78 respectively it records 156/154 coordinate squares and 123/120 induced six-cycles formed by deleting antipodal pairs from three-dimensional faces. These explicit vertex sets can supply valid cycle cuts. They are finite graph data, not a path exclusion or a speed claim.

## Next formulation and its limits

Select 94 vertices of the allowed graph, 47 of each parity. Select exactly two endpoints, require t to be one of them, and impose degree 1 at selected endpoints and degree 2 at other selected vertices. Degree equations apply only when the vertex is selected. Every target path satisfies these constraints. Both possible joining vertices have even parity, so a 93-edge partner has an odd second endpoint. Hence endpoint variables are needed only for the 79 odd vertices; exactly one is chosen, while the joining endpoint is fixed. This restriction follows from alternating parity and leaves the endpoint location free. The selected graph can also contain disjoint cycles. A simple path component contains both degree 1 vertices, since every component has an even number of odd-degree vertices. Every other component is a cycle. For each such cycle C, the inequality $\\sum_{{v\\in C}}x_v\\le |C|-1$ is valid: an induced path cannot contain all vertices of a cycle. Indeed, choose the cycle vertex appearing last along the induced path. Its two distinct cycle neighbours would both have to be its single preceding path vertex, a contradiction. Excluding cycles iteratively preserves every target path; a connected selection supplies the desired witness.

Round 190 contains an existing component/cut loop and round 192 has variable endpoint indicators. The former's saved restricted exclusion required zero dynamic cuts, so it supplies no speed evidence for the proposed use. Remove all former fixed-second-endpoint, overlap, exchange, omission and crossing restrictions. The old 93 search used an auxiliary circuit; no use of the alternative for this query was found in the inspected records. This is a change of method and scope, without a novelty claim. The written degree/cycle equivalence and its concrete implementation should receive Lean/source checking as introduced next round; this round does not claim that check.

{next_step}

## Maintained frontier and goal state

The interval remains $191≤a(9)≤233$. The contributor 233 theorem is unconditional in its saved final assembly; independent full rebuilding remains pending. Contributor b0521e1d and final audit b65d30ca are unchanged. The 196 conjecture is unresolved. Only retained [1,4] is exhausted among 28 six-coordinate choices ; 27 remain unresolved. Other active case states are unchanged.

Goal ACTIVE. {intent['pause_policy']} No substantial-result or prolonged-stall pause is declared. No email was sent; no sending connector is available. Both existing manuscripts compile and match their repository mirrors. All authors and hyperlink settings are preserved. Last full-paper review 210; next 220.
'''
write(H / 'MATHEMATICAL_NOTE.md', note)
handoff = f'''# Current state after round 217

Goal ACTIVE. {intent['pause_policy']} No email sent; no sending connector is available.

Read milestones/217-long-parent-search/MATHEMATICAL_NOTE.md, logs/compatible-parent-review.md and data/completion.json. No new Lean theorem or numerical bound this round. The native engine and accepted216 propagation proofs are unchanged. The saved transition audit is distinct from a complete native execution certificate.

The interval remains $191≤a(9)≤233$. Contributor b0521e1d and final audit b65d30ca are unchanged; independent full rebuild of233 remains pending. No different parent or longer snake was obtained.

| Case | Retained pair | Saved milestone | Cumulative jobs | Pending | Cumulative nodes |
|---|---|---|---:|---:|---:|
|22|[0,6]|217-long-parent-search|{s['jobs']}|{s['pending']}|{s['nodes']:,}|
|23|[0,5]|211-subset-capacity|296|11|3,721,372|
|24|[0,4]|209-slice-capacity|150|8|9,625,900|
|9|[3,4]|209-slice-capacity|150|3|8,142,891|

Case 22 hash: {s['state_sha256']}. IMPORTANT: version2 state counters and receipt paths are local to 217. The summary is cumulative and links216's cumulative1140-job baseline. Only retained [1,4] is exhausted among 28 choices ; 27 remain unresolved.

Next: {next_step}

Exact sources: outputs/snake8_witness.json; work/layer_search.py and work/exact_search.py; outputs/layer_search.json and layer_threshold.json. Do not call layer_search.seed(), which rewrites the archived witness. Read the immutable JSON. Candidate replacement code: milestones/190-exchange-constraints/scripts/cycle_cuts.py and milestones/192-moving-ports/scripts/joint_replacement.py. Graph lists and static cycle vertex sets are in217/data/complement-graph.json. Existing joining proofs are in outputs/LayerJoining.lean and IntegerLayerBridge.lean, with later checked copies in188/189. Preserve endpoint orientation when constructing Q9.

One heavy worker only; startup>=1GiB free, reserve>=768MiB, private<=256MiB; Lean60s,-j1,-s8192,55s startupwait. No software tests unless requested. Never restart a live process after an observation timeout. Preserve frozen evidence and unrelated .gitignore/milestone50 edits. Keep assertion checks enabled.

Editor originals: D:/Codex/2026-10-13/new-chat/outputs/snake9_research.tex and snake9_frontier_explanation.tex. Both compile and match paper mirrors. Preserve all authors and hypersetup. Compile frontier first, main last. Full-paper review next 220. Publish only the exact scoped manifest.
'''
write(R / 'handoff/CURRENT_STATUS.md', handoff)
write(R / 'handoff/NEXT_AGENT_PROMPT.md', handoff)
header = f'''# Current result after round 217

The longer continuation examines {s['local_nodes']:,} additional nodes; case[0,6] remains open with {s['pending']} regions. Review identifies a direct unresolved target: a 93-edge partner for the saved 98-edge Q8 path would give192 edges in Q9. This route does not first require a different optimal parent. Both endpoint queries remain unresolved; the next search will use degree conditions and cycle exclusions.

The interval remains $191≤a(9)≤233$. No new construction or numerical bound was obtained. The contributor 233 proof's independent full rebuild remains pending. The goal is active.

Read [the argument](milestones/217-long-parent-search/MATHEMATICAL_NOTE.md), [evidence](milestones/217-long-parent-search/data/completion.json), [handoff](handoff/CURRENT_STATUS.md) and [frontier explanation](paper/snake9_frontier_explanation.tex).

## Earlier checkpoints

'''
old = (R / 'README.md').read_text(encoding='utf-8')
assert not old.startswith('# Current result after round 217')
write(R / 'README.md', header + old)
write(H / 'README.md', '''# Round 217: longer parent search and direct partner target

Read MATHEMATICAL_NOTE.md, data/completion.json and logs/compatible-parent-review.md. The unchanged native engine continues the saved case; the state remains open. A direct93-edge partner for the saved 98-edge parent is the next construction priority. Version2 state counters are local and summary totals are cumulative. Goal ACTIVE.
''')
print('FROZEN_ROUND217; ACTIVE; DIRECT93_NEXT')
