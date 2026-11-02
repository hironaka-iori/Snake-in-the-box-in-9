"""Verify successful receipts and freeze the forty-rule retention checkpoint."""
from pathlib import Path
import datetime, hashlib, json, re, subprocess
HERE=Path(__file__).resolve().parents[1]; ROOT=HERE.parents[1]
read=lambda p:json.loads(p.read_text(encoding='utf-8-sig'))
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
old=ROOT/'milestones/79-retained-edge-guards'
summary=read(old/'data/proof-summary.json')
for row in summary['receipts']:
    path=old/row['receipt']; assert sha(path)==row['sha256']
    r=read(path)
    for sub,ext,key in [('lean','.lean','source_sha256'),('build','.olean','olean_sha256'),('logs','.log','log_sha256')]:
        assert sha(old/sub/(row['module']+ext))==r[key]
modules=['PositionTransfer','GuardTransfer','JointCountBridge','JointCountTags',
         'MultiCentreCount','CapCatalogue','SumCatalogue','ShortRetention']
rows=[]
for name in modules:
    path=HERE/'data'/f'{name}-audit.json'; r=read(path)
    assert r['status']=='PASS_LEAN_MODULE' and r['exit_code']==0
    for sub,ext,key in [('lean','.lean','source_sha256'),('build','.olean','olean_sha256'),('logs','.log','log_sha256')]:
        assert sha(HERE/sub/(name+ext))==r[key]
    assert not re.search(r'\b(sorry|admit|native_decide)\b',(HERE/'lean'/f'{name}.lean').read_text())
    assert r['inherited_summary_sha256']==sha(old/'data/proof-summary.json')
    for dep,digest in r['dependencies'].items():
        assert sha(HERE/'data'/f'{dep}-audit.json')==digest
    if 'short_support_sha256' in r:
        assert sha(HERE/'data/short-support.json')==r['short_support_sha256']
    for audit in r['theorem_audits']:
        assert set(audit['axioms']) <= {'propext','Classical.choice','Quot.sound'}
    rows.append(dict(module=name,receipt=path.relative_to(HERE).as_posix(),
                     sha256=sha(path),audits=len(r['theorem_audits'])))
assert sum(r['audits'] for r in rows)==66
support=read(HERE/'data/short-support.json'); assert len(support['modules'])==970
for r in support['modules'].values():
    assert sha(Path(r['source']))==r['source_sha256']
    assert sha(Path(r['object']))==r['object_sha256']
for path,digest in support['prior_audit_sha256'].items(): assert sha(ROOT/path)==digest
for name,r in read(HERE/'data/copied-joint-sources.json').items():
    assert sha(Path(r['origin']))==sha(HERE/'lean'/f'{name}.lean')==r['source_sha256']
comparison=read(HERE/'data/builder-comparison.json')
assert comparison['status']=='PASS_EXACT_RECOVERED_BUILDER_LOOP'
assert comparison['candidate_pairs']==23561280 and comparison['reconstructed_source_rules_match']
assert comparison['mask_sha256']=='1ff64848a9814704b92da43de676f5b2e75145315bdd7450d8fa46734acd9e94'
for path,digest in comparison['source_sha256'].items(): assert sha(ROOT/path)==digest
paper=ROOT/'paper/snake9_research.tex'
editor=Path('D:/Codex/2026-10-13/new-chat/outputs/snake9_research.tex')
assert sha(paper)==sha(editor)=='3c67d4c168ee7fe463f2ea49da3459f2178ee2a655fd45f9ed374f88126f43dd'
result=dict(status='PASS_FORTY_SHORT_RULE_RETENTION',receipts=rows,printed_theorem_audits=66,
    pinned_support_objects=970,inherited_summary_sha256=sha(old/'data/proof-summary.json'),
    short_support_sha256=sha(HERE/'data/short-support.json'),
    copied_joint_sources_sha256=sha(HERE/'data/copied-joint-sources.json'),
    builder_comparison_sha256=sha(HERE/'data/builder-comparison.json'),paper_sha256=sha(paper),
    limitations=['Existing certificate objects reused; full inherited closure not rebuilt.',
      'Concrete reference union, history exclusions and retained-array membership remain.',
      'Credit interpretation and complete potential replay remain.',
      'Five target local share theorems remain; no new global upper bound.'])
(HERE/'data/proof-summary.json').write_text(json.dumps(result,indent=2)+'\n')
refs={ref:subprocess.check_output(['git','-c','core.commitGraph=false','rev-parse',ref],cwd=ROOT,text=True).strip()
      for ref in ['HEAD','origin/main','origin/research/unconditional-241']}
checkpoint=dict(status=result['status'],recorded_at=datetime.datetime.now(datetime.timezone.utc).isoformat(),
    git_refs_before_commit=refs,unconditional_edge_interval=[191,235],conditional_target=234,
    upper_bound_evidence='Inspected contributor theorem and saved audit; no fresh complete independent rebuild.',
    paper_revision=76,next_scheduled_paper_revision=86,paper_sha256=sha(paper),
    printed_theorem_audits=66,short_rules=40,candidate_pairs=23561280,
    case7305_complete=True,remaining_local_share_cases=[7301,7302,7303,7307,7308],
    completed_share_model_mean='483',completed_share_model_range=551,
    proof_summary_sha256=sha(HERE/'data/proof-summary.json'),
    independent_review_sha256=sha(HERE/'audit/final-review.md'),
    process_scope='This round launched no long proof replay. Completed checks have exited.')
(HERE/'data/checkpoint.json').write_text(json.dumps(checkpoint,indent=2)+'\n')
print(result['status'],'66 audits; 970 pinned support objects; exact builder inputs verified')
