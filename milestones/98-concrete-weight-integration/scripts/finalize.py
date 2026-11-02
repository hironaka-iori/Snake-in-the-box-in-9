"""Freeze successful proof integration and update the current research handover."""
from pathlib import Path
import datetime,hashlib,json,re,subprocess,sys
HERE=Path(__file__).resolve().parents[1];ROOT=HERE.parents[1]
read=lambda p:json.loads(p.read_text(encoding='utf-8-sig'))
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
assert not (HERE/'data/check.lock').exists()
subprocess.run([sys.executable,'-B','-X','utf8',str(HERE/'scripts/audit.py')],check=True)
summary=read(HERE/'data/proof-summary.json');prior=HERE.parent/'97-geometric-credit-integration/data/checkpoint.json';old=read(prior)
paper=ROOT/'paper/snake9_research.tex'
assert sha(paper)==old['paper_sha256']==sha(Path('D:/Codex/2026-10-13/new-chat/outputs/snake9_research.tex'))
case=ROOT/'milestones/73-countfree-share-catalogue/cases/case7302'
assert not (case/'data/proof-audit.json').exists()
assert sha(case/'logs/completion-record.json')==sha(ROOT/'milestones/93-defined-graph-potential/data/case7302-completion-observation.json')
refs={ref:subprocess.check_output(['git','-c','core.commitGraph=false','rev-parse',ref],cwd=ROOT,text=True).strip() for ref in ['HEAD','origin/main']}
assert refs['HEAD']==refs['origin/main']
c=dict(status='PASS_ACTUAL_WEIGHT_CHARGE_AND_CONDITIONAL_UPPER_BOUND_CHAIN',previous_goal_turn='progress',
    recorded_at=datetime.datetime.now(datetime.timezone.utc).isoformat(),proof_summary_sha256=sha(HERE/'data/proof-summary.json'),
    theorem_audits=summary['theorem_audits'],modules=len(summary['modules']),
    actual_completed_weight_checked=True,actual_conditional_weight_checked=True,
    actual_total_charge_checked=True,full_key_walk_checked=True,
    completed_upper235_assembly_checked=True,conditional_upper234_assembly_checked=True,
    pending_reference_catalogues=['AllRefuted6K235','AllRefuted236'],
    pending_conditional_local_cases=[7301,7302,7303,7307,7308],pending_share_floors=[16,18,16,16,16],
    completed_potential=dict(slope=483,range=551,defined_graph_certificate_checked=False),
    conditional_potential=dict(slope=496,range=602,defined_graph_certificate_checked=False),
    saved_graph_weight_reconstruction_sha256=sha(HERE/'data/weight-model-audit.json'),
    unconditional_edge_interval=[191,235],upper_bound_evidence=old['upper_bound_evidence'],conditional_target=234,
    case7302_state='STOPPED_AFTER_CHECK1_TIMEOUT_900_SECONDS',case7302_source_record_unchanged=True,
    paper_revision=96,next_scheduled_paper_revision=106,paper_sha256=sha(paper),
    prior_checkpoint=prior.relative_to(ROOT).as_posix(),prior_checkpoint_sha256=sha(prior),git_refs_before_commit=refs,
    next_task='Certify the completed and floor18 potentials and their ranges on every row of the same defined graph. Restore the two reference-catalogue closures and continue the five local refutations; preserve old case7302 evidence.',
    scope='Complete actual-weight and charge integration, plus upper-bound assembly with explicit remaining hypotheses. No new unconditional numerical bound or exact optimum.')
(HERE/'data/checkpoint.json').write_text(json.dumps(c,indent=2)+'\n')
latest=('Latest continuation: [milestone 98](milestones/98-concrete-weight-integration/README.md) checks the remaining concrete share rules, both count-free profiles, the complete actual edge weight, the 21-count boundary saving and total charge. The full-key walk and numerical bound assembly are checked with their remaining hypotheses explicit. The global interval remains 191 through 235; 234 remains conditional.')
priority=('Next research priority: certify both potentials on every row of the defined graph, using the exact checked weights. The completed profile uses slope 483 and range 551; the conditional floor-18 profile uses slope 496 and range 602. Two reference-catalogue closures and five conditional local shares remain. Paper revision 96 is unchanged; the next scheduled full revision is 106.')
for name in ['README.md','COLLABORATION.md']:
    p=ROOT/name;s=p.read_text()
    for prefix,value in [('Latest continuation:',latest),('Next research priority:',priority)]:
        s,n=re.subn('^'+re.escape(prefix)+'.*$',lambda _:value,s,count=1,flags=re.M);assert n==1
    p.write_text(s)
p=ROOT/'milestones/README.md';s=p.read_text();i=s.index('- [Milestone 97:')
assert '- [Milestone 98:' not in s
s=s[:i]+'- [Milestone 98: actual weights, total charge and conditional bound assembly](98-concrete-weight-integration/README.md). Both floor profiles are integrated with the full edge key; potential certificates, reference closures and five conditional shares remain.\n\n'+s[i:];p.write_text(s)
p=ROOT/'RESEARCH_LEDGER.md';s=p.read_text();assert '## Milestone 98:' not in s
p.write_text(s+'\n\n## Milestone 98: actual weights and the remaining upper-bound hypotheses\n\n'+latest+'\n\n'+priority+'\n')
(HERE/'README.md').write_text(f'''# Milestone 98: actual weights and the upper-bound proof chain

The complete edge-weight interpretation and total charge budget passed Lean
for the completed floor profile. The conditional profile retains precisely
five local refutations, with required floors (16,18,16,16,16). Both profiles
use the same actual five-centre sum and preserve saturated count intervals.

The full-key walk and potential summation are checked. The resulting upper235
and upper234 statements retain two reference-catalogue assumptions and the
appropriate potential and range hypotheses on every row of the defined graph.
The upper234 statement also retains the five local refutations. No new
unconditional numerical upper bound is claimed.

There are {len(summary['modules'])} checked modules and {summary['theorem_audits']}
theorem audits, including reused local roots and auxiliary statements. An
independent reconstruction agrees on all 4,947,008 saved full keys in 791
contexts for both profiles. Saved-array agreement does not discharge the
potential hypotheses on the defined graph.

Read the [mathematical note](mathematical-note.md),
[checkpoint](data/checkpoint.json), [proof summary](data/proof-summary.json),
and [independent weight audit](audit/weight-model-audit.md).
Exact compiler attempts, source snapshots and dependencies are preserved.
The shared object overlay is an ignored build cache. Existing proof objects
are reused; no complete clean dependency rebuild is asserted.

The maintained interval is $191\\le a(9)\\le235$ edges. The contributor upper
bound retains its archived evidence and pending independent rebuild. The exact
optimum is unresolved. Paper revision 96 is unchanged; the next scheduled full
revision is 106. Original case7302 evidence remains stopped and unchanged.
''')
print(c['status'],c['modules'],'modules;',c['theorem_audits'],'audits')
