"""Verify the cycle, arithmetic and conditional sensitivity receipts."""
from pathlib import Path
import datetime,hashlib,json,subprocess
HERE=Path(__file__).resolve().parents[1];ROOT=HERE.parents[1]
read=lambda p:json.loads(p.read_text());sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
g=read(HERE/'data/graph-audit.json');a=read(HERE/'data/lean-audit.json');t=read(HERE/'data/target-sensitivity.json')
assert g['status']=='PASS_UNSATURATED_ATTAINING_CYCLE'
assert a['status']=='PASS_UNSATURATED_OBSTRUCTION_ARITHMETIC' and a['exit_code']==0
assert a['graph_audit_sha256']==sha(HERE/'data/graph-audit.json')
for part,ext,key in [('lean','.lean','source_sha256'),('build','.olean','object_sha256'),('logs','.log','log_sha256')]:
    assert sha(HERE/part/('UnsaturatedCycle'+ext))==a[key]
assert len(a['theorem_audits'])==6
for row in a['theorem_audits']:assert set(row['axioms'])<={'propext','Classical.choice','Quot.sound'}
for path,digest in g['source_sha256'].items():assert sha(ROOT/path)==digest
for path,digest in t['input_sha256'].items():assert sha(ROOT/path)==digest
assert t['affected_pending_cases']==[7302,7307] and t['hypothetical_cycle_mean']=='497'
paper=ROOT/'paper/snake9_research.tex';editor=Path('D:/Codex/2026-10-13/new-chat/outputs/snake9_research.tex')
assert sha(paper)==sha(editor)=='3c67d4c168ee7fe463f2ea49da3459f2178ee2a655fd45f9ed374f88126f43dd'
summary=dict(status='PASS_UNSATURATED_CYCLE_OBSTRUCTION',printed_theorem_audits=6,
    graph_audit_sha256=sha(HERE/'data/graph-audit.json'),lean_audit_sha256=sha(HERE/'data/lean-audit.json'),
    target_sensitivity_sha256=sha(HERE/'data/target-sensitivity.json'),
    scope='Finite graph and rational arithmetic; no new global bound. Conditional target calculation concerns one cycle only.')
(HERE/'data/proof-summary.json').write_text(json.dumps(summary,indent=2)+'\n')
refs={ref:subprocess.check_output(['git','-c','core.commitGraph=false','rev-parse',ref],cwd=ROOT,text=True).strip()
      for ref in ['HEAD','origin/main','origin/research/unconditional-241']}
checkpoint=dict(status=summary['status'],recorded_at=datetime.datetime.now(datetime.timezone.utc).isoformat(),
    git_refs_before_commit=refs,unconditional_edge_interval=[191,235],conditional_target=234,
    upper_bound_evidence='Inspected contributor theorem and saved audit; no fresh full independent rebuild.',
    finite_model_mean=483,finite_model_potential_range=551,strict_criterion_deficit_at_zero_range=2319,
    targeted_pending_cases=[7302,7307],conditional_witness_mean=497,
    remaining_local_share_cases=[7301,7302,7303,7307,7308],
    paper_revision=76,next_scheduled_paper_revision=86,paper_sha256=sha(paper),
    proof_summary_sha256=sha(HERE/'data/proof-summary.json'),
    independent_review_sha256=sha(HERE/'audit/review.md'),printed_theorem_audits=6,
    process_scope='All graph and Lean checks in this round have exited. No long replay was started.')
(HERE/'data/checkpoint.json').write_text(json.dumps(checkpoint,indent=2)+'\n')
print(summary['status'],'6 audits; graph and targeted-witness inputs verified')
