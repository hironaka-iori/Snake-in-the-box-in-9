"""Save the completed continuation, evidence limits and direct-construction handoff."""
from pathlib import Path
from datetime import datetime, timezone
import hashlib, json, re

H = Path(__file__).resolve().parents[1]
R = H.parents[1]
P = H.parent / '217-long-parent-search'
D = Path('D:/Codex/2026-10-13/new-chat/outputs')
def sha(p): return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def write(p, s): p.write_text(s.strip() + '\n', encoding='utf-8', newline='\n')
def save(p, x): write(p, json.dumps(x, indent=2))
def read(p): return json.loads(p.read_bytes())

assert not (H / 'data/partner-search.lock').exists()
s = read(H / 'data/search-summary.json')
assert all(x['status'] in ['UNKNOWN','INFEASIBLE'] for x in s['roots'])
proofs = []
for name, count in [('Cycle218', 2), ('PartnerParity218', 3)]:
    p = H / 'data' / (name + '-audit.json'); d = read(p)
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
audit = read(H/'data/partner-audit.json')
assert audit['status'] == 'PASS_SAVED_MODEL_AND_RECORD_AUDIT'
assert len(audit['retry_roots']) == 2
for path, digest in audit['pins'].items(): assert sha(H/path) == digest
for row, checked in zip(s['roots'], audit['retry_roots']):
    assert row['root'] == checked['root'] and row['status'] == checked['status']
    assert row['result_sha256'] == checked['result_sha256']
frozen = {}
for case, folder, digest in [
    ('22','217-long-parent-search','79d48c05cfc33461671656122c3fa003b2488cc344fc6adf89dd532fb6502452')]:
    p=H.parent/folder/'data'/('case-'+case)/'state.json'; assert sha(p)==digest
    frozen[case]={'path':str(p.relative_to(R)),'sha256':digest}
for case, folder in [('23','211-subset-capacity'),('24','209-slice-capacity'),('9','209-slice-capacity')]:
    p=H.parent/folder/'data'/('case-'+case)/'state.json'
    previous=read(P/'data/completion.json')['frozen_other_states'][case]
    assert sha(p)==previous['sha256']; frozen[case]=previous
intent=read(H/'data/round-intent.json')
refinement=read(H/'data/graph-refinement.json')
assert refinement['source_sha256']==sha(H/'data/complement-graph.json')
next_step=('Evaluate the explicit linear relaxation of the fixed-parent partner model at both roots. '
           'For each non-root vertex with selection x, endpoint indicator e, ambient degree d and selected-neighbour sum s, '
           'replace conditional degree by 2x-e <= s <= d-(d-2)x-e, with 0<=e<=x<=1 and e=0 at other even vertices. '
           'Keep root selection/degree1, one free odd endpoint, parity balance and every verified cycle inequality. '
           'Maximize total selection after relaxing Boolean variables to [0,1]. '
           'An upper bound below94 would exclude this parent target only after an exact rational dual certificate is checked, preferably in Lean. '
           'A bound at least94 would show that this relaxation is insufficient, not that a partner exists. '
           'Do not repeat an unchanged long query or claim a global Q9 upper bound from a fixed-parent result.')
completion={'round':218,'status':'PROGRESS','previous_goal_turn':'PROGRESS','started_utc':intent['started_utc'],
    'utc':datetime.now(timezone.utc).isoformat(),'goal_state':'ACTIVE','pause_policy':intent['pause_policy'],
    'email_sent':False,'email_limitation':'No sending connector available.','interval':[191,233],
    'contributor_revision':intent['contributor_at_start'],'contributor_changed':False,'independent_233_rebuild':False,
    'new_q9_record':False,'new_global_bound':False,'accepted_new_modules':2,'theorem_reports':5,'proofs':proofs,
    'search':s,'first_attempt':'Interrupted on sampled memory limit before a model/result existed; no mathematical inference.',
    'retry_environment':{k:'1' for k in ['OPENBLAS_NUM_THREADS','OMP_NUM_THREADS','MKL_NUM_THREADS','NUMEXPR_NUM_THREADS']},
    'partner_audit_sha256':sha(H/'data/partner-audit.json'),'frozen_parent_search_states':frozen,
    'six_coordinate_unresolved':27,'complete_native_certificate':False,'software_tests_created_or_run':False,
    'compile_success':True,'review_hashes':{name:sha(H/'logs'/name) for name in
        ['cycle-proof-review.md','partner-parity-proof.md','partner-model-review.md','partner-result-review.md']},
    'graph_refinement_sha256':sha(H/'data/graph-refinement.json'),'next_step':next_step}
save(H/'data/completion.json',completion)
rows='\n'.join(f"|{x['root']}|{x['status']}|{x['solver_seconds']:.3f}|{x['branches']:,}|{x['conflicts']:,}|{x['dynamic_cycle_cuts']}|" for x in s['roots'])
note=r'''# Round 218: direct partner queries and necessary inequalities

The target is a 93-edge induced path in the 158-vertex allowed graph of the saved 98-edge Q8 parent, rooted at endpoint 0 or 78. Its other endpoint is free. Only the parent's other 98 vertices are forbidden. A compatible partner would yield $98+93+1=192$ Q9 edges. No such construction was obtained this round.

## Necessary constraints and their proofs

The model selects 94 vertices, with degree one at the prescribed endpoint and one free endpoint, and degree two at all other selected vertices. Degree equations are conditional on selection. Both prescribed vertices have even parity. Consecutive cube edges reverse parity, so a 93-edge partner has 47 vertices of each parity and an odd free endpoint.

PartnerParity218 checks this alternation using the adjacency of an actual induced path of equal-length Boolean words. It then checks the final endpoint parity and both 47-vertex counts. No alternation assumption is substituted for the actual path edges. The numerical integer-to-word interpretation remains distinct from this theorem.

For any simple cycle C and a selection S drawn from an actual induced path, $|S\cap C|\le |C|-1$. If every cycle vertex occurred in the path, choose the last one. Its two distinct cycle neighbours would both occur earlier, and inducedness would force each to be the unique preceding path vertex. This is impossible. Cycle218 checks the noncontainment argument and the counting inequality, reusing the accepted maximum-position argument from round 196. Extra cycle chords are allowed. Two new modules pass with five dependency reports using only the standard foundational axioms.

The selected-degree conditions can still admit separate cycles. The initial model adds 279 cuts at root 0 and 274 at root 78, covering the saved coordinate squares and six-cycles obtained by deleting antipodal vertices of three-faces. Each returned separate cycle would produce another valid cut. A connected solution must also pass direct all-pairs validation in Q8 and Q9. These generic Lean results do not certify numerical cycle extraction, constraint serialization or native solver exhaustion.

## Native outcomes

| Root | Status | Solver seconds | Branches | Conflicts | Dynamic cuts |
|---|---|---:|---:|---:|---:|
'''+rows+r'''

UNKNOWN provides neither a construction nor an exclusion. Any INFEASIBLE result has only fixed-parent native-solver scope and requires a separate contradiction certificate. No global upper bound is inferred. The model uses arbitrary partner shapes, with no isometric-copy, fixed-prefix, overlap or replacement restriction. No controlled speed comparison against the old circuit formulation is established.

The first invocation was stopped after a sampled private-memory reading of 590,295,040 bytes, before any model or result artifact was produced. Its sources and receipt remain preserved in data/root-0. A separate invocation limits numerical-library threads to one. The mathematical model and solver parameters are unchanged. The retry's outputs, exact exported models, resource observations and source pins are retained in data/threads1. The independent record audit reconstructs the allowed graphs and compares the exported model with the intended degree, parity and cycle constraints. It does not replay a solver proof.

## Symmetry and next calculation

Rooted graph-colour refinement reaches 158 singleton classes in both allowed graphs: class counts are 8, 95, 155, 158 for root 0 and 8, 95, 153, 158 for root 78. Any root-fixing graph automorphism preserves each refinement step, so these finite calculations leave no nonidentity rooted graph automorphism to exploit. This concerns the two fixed allowed graphs; it does not exclude broader transformations of whole snakes. This is a native finite calculation without a new Lean certificate. No symmetry restriction was imposed on either query.

The conditional degree equation has an exact linear form. Let x and e be Boolean selection and endpoint indicators with e<=x, let d be the available degree, and let s be the selected-neighbour count. Since 0<=s<=d, the implication x=1 => s=2-e is equivalent to

\[
2x-e\le s\le d-(d-2)x-e.
\]

For x=0, e=0 and the bounds reduce to 0<=s<=d. For x=1, both bounds equal 2-e. Signed arithmetic is intended. Relaxing x and e to the interval [0,1] therefore gives a necessary linear relaxation. This short algebraic derivation is written and source-reviewed; no new Lean result or solved linear program is claimed for it this round.

'''+next_step+r'''

## Maintained research state

The recorded interval remains $191\le a(9)\le233$. Independent full rebuilding of the contributor's233 proof remains pending; contributor b0521e1d and saved final audit b65d30ca are unchanged. The 196 conjecture is unresolved. The prior parent-search states are unchanged: case 22 remains at 1260 cumulative jobs,11,724,609 nodes and eight unfinished regions; 27 of 28 six-coordinate choices remain unresolved.

The goal remains ACTIVE under the user's own-work pause condition. Contributor work alone cannot trigger a pause. No pause is declared and no email is sent; no sending connector is available. Both existing manuscripts compile and exactly match their repository mirrors. Author order and hyperlink settings are preserved. Full-paper review is due at round 220.
'''
write(H/'MATHEMATICAL_NOTE.md',note)
handoff=f'''# Current state after round 218

Goal ACTIVE. {intent['pause_policy']} No email sent; no sending connector is available.

Read milestones/218-direct-partner/MATHEMATICAL_NOTE.md and data/completion.json. Cycle218 and PartnerParity218 pass with five reports: actual-path cycle occupancy and93-edge parity/endpoints/counts. Numerical encoding and native exhaustion are separate obligations.

{rows}

The direct partner queries remain subject to their saved statuses; UNKNOWN gives no exclusion. No192-edge witness or new global bound was obtained. The interval remains191<=a(9)<=233, with independent full rebuilding of233 pending. Contributor b0521e1d and final audit b65d30ca are unchanged.

Next: {next_step}

The first run exceeded memory during startup and produced no mathematical result. Preserve data/root-0 and its original source snapshots. The retry is data/threads1/root-0 and root-78. Set OPENBLAS_NUM_THREADS, OMP_NUM_THREADS, MKL_NUM_THREADS and NUMEXPR_NUM_THREADS to1 before numerical imports. Keep one heavy worker, startup>=1GiB free, reserve>=768MiB, private<=256MiB, Lean60s,-j1,-s8192,55s startupwait. No software tests unless requested. Never restart a live handle after an observation timeout.

Parent search remains frozen in217: case 22 state SHA79d48c05cfc33461671656122c3fa003b2488cc344fc6adf89dd532fb6502452,1260 cumulative jobs,11,724,609nodes,8pending. State counters are local to217; summary totals are cumulative. Other cases23/24/9 remain in211/209/209. Only retained[1,4] is exhausted;27six-coordinate choices remain unresolved. Do not overwrite prior evidence.

Existing editor originals remain D:/Codex/2026-10-13/new-chat/outputs/snake9_research.tex and snake9_frontier_explanation.tex. Both compile and match paper mirrors. Preserve all three authors and hypersetup. Compile frontier first, main last. Full-paper review220. Preserve unrelated .gitignore and milestone50 edits. Publish only the exact scoped manifest.
'''
write(R/'handoff/CURRENT_STATUS.md',handoff);write(R/'handoff/NEXT_AGENT_PROMPT.md',handoff)
header=f'''# Current result after round 218

Two new Lean modules check necessary cycle and parity constraints for the direct93-edge compatible-partner target. Endpoint queries return {', '.join(str(x['root'])+':'+x['status'] for x in s['roots'])}. No longer snake or global bound is obtained. The goal remains active; next is an explicit linear relaxation and, if strong enough, an exact weighted inequality certificate.

Read [the argument](milestones/218-direct-partner/MATHEMATICAL_NOTE.md), [evidence](milestones/218-direct-partner/data/completion.json), [handoff](handoff/CURRENT_STATUS.md) and [frontier explanation](paper/snake9_frontier_explanation.tex).

## Earlier checkpoints

'''
old=(R/'README.md').read_text(encoding='utf-8');assert not old.startswith('# Current result after round 218')
write(R/'README.md',header+old)
write(H/'README.md','''# Round 218: direct compatible-partner queries

Read MATHEMATICAL_NOTE.md and data/completion.json. Cycle218 and PartnerParity218 pass with five reports. Native outcomes retain their fixed-parent scope. The first resource-stopped attempt is separate from the thread-limited retry. No new numerical bound. Goal ACTIVE.
''')
print('FROZEN_ROUND218; ACTIVE; LINEAR_RELAXATION_NEXT')
