"""Freeze the exact relaxation result and its resumable research record."""
from pathlib import Path
from datetime import datetime,timezone
import hashlib,json,re
H=Path(__file__).resolve().parents[1];R=H.parents[1]
D=Path('D:/Codex/2026-10-13/new-chat/outputs')
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def read(p):return json.loads(Path(p).read_bytes())
def write(p,s):Path(p).write_text(s.strip()+'\n',encoding='utf-8',newline='\n')
def save(p,x):write(p,json.dumps(x,indent=2))
assert not (H/'data/lp-search.lock').exists()
proofs=[]
for name in ['Degree219','CyclePotential219']:
    p=H/'data'/(name+'-audit.json');a=read(p)
    assert a['status']=='PASS' and a['exit_code']==0 and a['stop_reason'] is None
    for pk,hk in [('source','source_sha256'),('object','olean_sha256'),('log','log_sha256')]:assert sha(a[pk])==a[hk]
    for path,digest in a['dependencies'].items():assert sha(path)==digest
    assert len(a['axioms'])==4
    assert all(set(q['axioms'])<={'propext','Classical.choice','Quot.sound'} for q in a['axioms'])
    proofs.append({'module':name,'receipt':str(p.relative_to(R)),'sha256':sha(p),'reports':4})
for label in ['lp','cycles','rational']:
    a=read(H/'data'/(label+'-execution.json'))
    assert a['status']=='ACCEPTED_NATIVE_RESULT' and a['exit_code']==0 and a['stop_reason'] is None
    for name,digest in a['pins'].items():assert sha(H/name)==digest
    for channel in ['stdout','stderr']:assert sha(H/'logs'/(label+'-'+channel+'.log'))==a[channel+'_sha256']
linear=read(H/'data/linear-audit.json');rational=read(H/'data/rational-audit.json')
assert rational['status']=='PASS_EXACT_PRIMAL_AND_ALL_SIMPLE_CYCLE_CERTIFICATES'
for report in rational['models']:
    assert report['all_simple_cycle_inequalities_certified'] and report['target94']['objective']==[94,1]
    assert report['edge_potential_count']==337 and report['potential_edge_inequalities']==113232
    folder=H/'data'/('rational-'+str(report['root']))
    for name,digest in report['pins'].items():
        path=H/'data'/('edge-'+str(report['root']))/name if name=='model.json' else folder/name
        assert sha(path)==digest
docs={}
for name,receipt in [('snake9_frontier_explanation.tex','frontier-compile.json'),('snake9_research.tex','main-compile.json')]:
    p=D/name;assert p.read_bytes()==(R/'paper'/name).read_bytes()
    before=(H/'data'/('before-'+name)).read_text(encoding='utf-8');after=p.read_text(encoding='utf-8')
    assert re.search(r'\\author\{[^\n]*',before).group()==re.search(r'\\author\{[^\n]*',after).group()
    if name=='snake9_research.tex':
        assert re.search(r'\\hypersetup\{.*?\n\}',before,re.S).group()==re.search(r'\\hypersetup\{.*?\n\}',after,re.S).group()
    labels=re.findall(r'\\label\{([^}]+)\}',after);assert len(labels)==len(set(labels))
    assert set(re.findall(r'\\(?:ref|eqref|pageref)\{([^}]+)\}',after))<=set(labels)
    bib=set(re.findall(r'\\bibitem\{([^}]+)\}',after))
    assert {v.strip() for g in re.findall(r'\\cite\{([^}]+)\}',after) for v in g.split(',')}<=bib
    c=read(H/'data'/receipt);assert not c.get('isError',False)
    assert any(json.loads(t['text']).get('kind')=='success' for t in c['content'] if t['type']=='text')
    docs[name]={'editor':str(p),'mirror':str(R/'paper'/name),'sha256':sha(p),'compile_receipt':receipt,'compile_sha256':sha(H/'data'/receipt)}
save(H/'data/document-verification.json',{'scope':'Exact mirrors, authors/settings preservation, references and compilation success; no page-by-page visual audit.','documents':docs})
frozen=read(H.parent/'218-direct-partner/data/completion.json')['frozen_parent_search_states']
for v in frozen.values():assert sha(R/v['path'])==v['sha256']
intent=read(H/'data/round-intent.json')
next_step=('Separate induced-forest subset inequalities sum(y over E(U)) <= sum(x over U)-x_v for v in U. '
    'Put E_t=1 at the root and E_u=e_u elsewhere. Degree sums give '
    '2 sum(x over U)-sum(E over U)=2 sum(y over E(U))+sum(y over boundary(U)). '
    'The forest inequality is therefore equivalent to sum(y over boundary(U))+sum(E over U)>=2x_v. '
    'Use a dummy sink with capacity E_u from each vertex u, and undirected capacities y on allowed edges. '
    'A minimum v-to-sink cut separates all subset inequalities for v. First examine the exact round219 rational points. '
    'Add witnessed violated subsets to the LP, solve under the existing resource guard, and replace numerical conclusions with exact certificates. '
    'If the resulting bound remains above94, reconstruct and audit a rational94 assignment before claiming a barrier. '
    'Keep all-cycle occupancy cuts or exact all-cycle verification as a separate condition. '
    'The subset argument is written, but has no new Lean proof or numerical separation yet. Full-paper review is due in round220.')
completion={'round':219,'status':'PROGRESS','started_utc':intent['started_utc'],'utc':datetime.now(timezone.utc).isoformat(),
    'previous_goal_turn':intent['previous_goal_turn'],'goal_state':'ACTIVE','pause_policy':intent['pause_policy'],
    'email_sent':False,'email_limitation':'No email-sending tool available on current discovery.',
    'interval':[191,233],'contributor_revision':intent['contributor_at_start'],'contributor_changed':False,
    'independent_233_rebuild':False,'new_q9_record':False,'new_global_bound':False,
    'accepted_new_modules':2,'theorem_reports':8,'proofs':proofs,
    'linear_summary':read(H/'data/lp-summary.json'),'rational_summary':read(H/'data/rational-summary.json'),
    'exact_target94_both_roots':True,'all_simple_cycle_barrier':True,
    'linear_audit_sha256':sha(H/'data/linear-audit.json'),'rational_audit_sha256':sha(H/'data/rational-audit.json'),
    'frozen_parent_search_states':frozen,'six_coordinate_unresolved':27,
    'software_tests_created_or_run':False,'compile_success':True,
    'scope':'Generic Lean lemmas and independent exact finite arithmetic; numerical arrays and the full graph-to-model assembly are not one Lean theorem.',
    'next_step':next_step}
save(H/'data/completion.json',completion)
note=r'''# Round 219: exact limits of the compatible-partner relaxation

The direct target remains a93-edge induced path starting at endpoint0 or78 of the saved98-edge Q8 parent and avoiding its other98 vertices. Joining the two faces would give192 Q9 edges. This round gives no such path and no new global bound.

## Result

At both roots, the continuous degree and edge-product formulation admits an exact rational selection of94 vertices satisfying every simple-cycle occupancy inequality. Adding more inequalities of that cycle form cannot exclude the target in this continuous model. Integrality or other valid inequalities are required.

The source graph has158 vertices and337 edges at each root. Vertex variables x, free-endpoint variables e and edge variables y range in[0,1]. The root is selected with degree1, the odd endpoint variables sum to1, e<=x, and selected parity totals are equal. At every nonroot vertex, with available degree d and neighbour-selection sum s,

\[
2x-e\le s\le d-(d-2)x-e.
\]

For Boolean variables this is exactly the conditional selected-degree equation. Edge variables satisfy0<=y<=x at either endpoint and y>=x_u+x_v-1, forcing y=x_ux_v when x is Boolean. Incident-edge sums give the same selected degrees. Every odd-edge actual partner maps to these necessary rows. No connectivity, integrality, or solver-optimality claim follows for a rational point.

## Exact numerical evidence

| Root | Exact feasible cardinality, all cycles | Exact upper certificate |
|---|---|---|
|0|43286778654/441499285, approximately98.044957545|49022513/500000=98.045026|
|78|75253867064343/770614508036, approximately97.654360617|3051701/31250=97.654432|

Vertex-only upper certificates are108.36883 and107.110383. The edge formulation is substantially stronger, yet it still permits the target. Root78's upper certificate implies at most96 vertices for an actual odd-edge partner, by even integral cardinality; this is95 edges and has only fixed-parent scope. The old native97-edge exclusion at root0 is not recovered by this LP bound.

The upper certificates use integer scaleD=10^6 and weighted rows. Nonnegative weights multiply inequalities; signed weights multiply equalities. With residual r=Dc-A^T Y-E^T Z, box bounds give

\[
D c\cdot z\le b\cdot Y+f\cdot Z+\sum_i\max(r_i,0).
\]

Exact residual compensation makes the statement independent of numerical optimality or dual feasibility. The independent audit reconstructs every model row and recalculates all coefficients, residuals and bounds.

## Certification of every simple-cycle inequality

Write w_u=1-x_u. For each of337 deleted edges ab, an exact rational potential p satisfies p_a=0, |p_u-p_v|<=w_u+w_v on all other edges, and p_b+w_a+w_b>=2. Summing along the rest of any simple cycle containing ab, then adding the omitted edge, gives2 sum_C w>=2. Hence sum_C x<=|C|-1 for every simple cycle.

Each certificate has574 rational coordinates and337 potential systems. The independent checker verifies all model rows, all box bounds and113,232 potential-edge inequalities per root. Both minimum cycle costs equal1, attained on saved squares. This is an exact certificate, distinct from the earlier floating separation report that found no violated cycles at its tolerance.

Mix each rational assignment of cardinalityq>94 with the actual one-edge path[0,2] or[78,14]. Weight92/(q-2) on the larger assignment gives cardinality94 exactly. The weights are10154483555/10600945021 and70896534739312/73712638048271. Convexity preserves every row and cycle inequality. Both resulting assignments are saved and independently audited. They do not specify Boolean paths.

## Lean and execution scope

Degree219 passes with four reports: exact integer conditional-degree encoding, Boolean edge-product encoding, residual compensation and the weighted bound with coefficient expansion explicit. CyclePotential219 passes with four reports: path telescoping, the closing-edge deduction, the twice-counted cycle identity and cycle occupancy. Only standard foundational axioms occur. Numerical coefficient arrays and graph indexing remain independently audited native exact arithmetic; no claim of an end-to-end Lean certificate is made.

The baseline LP, floating cycle separation, and exact basis recovery are terminal with exit0 and no resource stop. The basis recovery supplies candidates only; the separate rational audit verifies their feasibility without invoking the optimizer or elimination procedure. Exact LP optimality is not asserted. Failed Lean elaboration attempts remain preserved. No software tests were created or run.

## Next deduction

For any vertex subsetU and v inU, an induced path gives

\[
\sum_{ab\in E(U)}y_{ab}\le\sum_{u\in U}x_u-x_v.
\]

The selected induced subgraph is a forest. Ifv is selected it is nonempty and has at most one fewer edge than vertices. Ifv is unselected the weaker bound still holds. Put E_t=1 at the root and E_u=e_u elsewhere. Summing the degree equations overU transforms the subset inequality into

\[
\sum_{ab\in\delta(U)}y_{ab}+\sum_{u\in U}E_u\ge2x_v.
\]

Thus one minimum-cut calculation for eachv can separate all such subsets: use capacitiesy on the original undirected edges and capacityE_u fromu to a new sink. These inequalities concern all selected edges of a subset, beyond occupancy of individual cycles. Their separation and influence on the bound are not computed in this round. The short counting argument is written; its actual-path Lean integration is pending.

## Maintained state

The interval remains191<=a(9)<=233. The contributor's233 final theorem is saved as unconditional, with its independent full rebuild still pending. The196 conjecture remains open. Remote main and the contributor branch were refreshed; contributor b0521e1d is unchanged. Earlier parent searches are frozen: case22 remains1260 cumulative jobs,11,724,609 nodes,8pending;27 of28 six-coordinate choices remain unresolved.

Both existing manuscripts compile and match their E: repository mirrors, with all authors and hypersetup preserved. The goal remains ACTIVE. This round changes the choice of inequalities; it does not meet the pause criterion of a major extremal result or prolonged lack of progress. Contributor work did not cause a pause. No email was sent because no sending tool is available. Full-paper review is due in round220.
'''
# Keep mathematical prose readable even beside concise numerical identifiers.
note=re.sub(r'(?<=[A-Za-z])(?=\d)|(?<=\d)(?=[A-Za-z])',' ',note)
write(H/'MATHEMATICAL_NOTE.md',note)
handoff=f'''# Current state after round219

Goal ACTIVE. {intent['pause_policy']} No pause trigger this round. No email sent; no sending tool is available.

Read milestones/219-linear-partner/MATHEMATICAL_NOTE.md and data/completion.json. Both exact continuous partner models admit cardinality94 even with every simple-cycle occupancy inequality. Data/rational-0 and rational-78 contain the exact points,337 potential systems each, and target94 mixtures. Both independent audits pass. Degree219 and CyclePotential219 pass with eight generic Lean results. Numerical arrays and graph assembly are separate from the Lean statements.

No192-edge witness or global upper improvement. Interval191<=a(9)<=233; independent full rebuild of contributor233 pending. Contributor b0521e1d and its saved final audit b65d30ca are unchanged.

Next: {next_step}

Frozen parent case22 remains in217-long-parent-search, SHA79d48c05cfc33461671656122c3fa003b2488cc344fc6adf89dd532fb6502452,1260 cumulative jobs,11,724,609 nodes,8pending. State counters are local to217, summary counters cumulative. Cases23/24/9 remain in211/209/209. Only retained[1,4] exhausted;27 six-coordinate choices remain unresolved. Do not overwrite earlier evidence.

Workdir E:/Snake-in-a-box. Set OPENBLAS_NUM_THREADS, OMP_NUM_THREADS, MKL_NUM_THREADS and NUMEXPR_NUM_THREADS to1 before numerical imports. One heavy worker, startup>=1GiB free, reserve>=768MiB, private<=256MiB, Lean60s,-j1,-s8192,55s startupwait. No software tests unless requested. Never restart a live handle after an observation timeout.

Editor originals D:/Codex/2026-10-13/new-chat/outputs/snake9_research.tex and snake9_frontier_explanation.tex; exact mirrors in paper/. Both compile. Preserve authors and hypersetup; compile frontier first, main last. Full-paper review220. Preserve unrelated .gitignore and milestone50 edits. Publish exact scoped manifest. Git flags core.commitGraph=false, maintenance.auto=false,gc.auto=0; constrained push pack flags from previous round.
'''
write(R/'handoff/CURRENT_STATUS.md',handoff);write(R/'handoff/NEXT_AGENT_PROMPT.md',handoff)
header='''# Current result after round219

Exact rational certificates show that both fixed-parent continuous partner models admit94 selected vertices even with every simple-cycle occupancy inequality. Thus adding cycle occupancy inequalities alone cannot exclude the192-edge joining target in this model. Two new Lean modules check eight supporting implications; the finite arrays have independent exact audits. No longer snake or new global bound. Goal ACTIVE; subset forest inequalities are next.

Read [the argument](milestones/219-linear-partner/MATHEMATICAL_NOTE.md), [evidence](milestones/219-linear-partner/data/completion.json), [handoff](handoff/CURRENT_STATUS.md), and [frontier explanation](paper/snake9_frontier_explanation.tex).

## Earlier checkpoints

'''
old=(R/'README.md').read_text(encoding='utf-8');assert not old.startswith('# Current result after round219')
write(R/'README.md',header+old)
write(H/'README.md','''# Round219: exact partner relaxations

Read MATHEMATICAL_NOTE.md and data/completion.json. Both roots admit exact fractional94-vertex selections satisfying every simple-cycle occupancy inequality. Two exact independent audits and eight generic Lean results are saved. No Boolean partner or global bound is inferred. Goal ACTIVE; subset forest inequalities next.
''')
print('FROZEN_ROUND219; ACTIVE; SUBSET_FOREST_INEQUALITIES_NEXT')
