"""Validate key handover evidence and save a bounded, exact file manifest."""
from pathlib import Path
import datetime
import hashlib
import json
import subprocess

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
M73 = ROOT / 'milestones/73-countfree-share-catalogue'
M74 = ROOT / 'milestones/74-graph-interpretation-audit'
read = lambda p: json.loads(p.read_text())


def sha(p):
    h = hashlib.sha256()
    with p.open('rb') as stream:
        for chunk in iter(lambda: stream.read(1024*1024), b''):
            h.update(chunk)
    return h.hexdigest()


def git(*args):
    return subprocess.check_output(['git', '-c', 'core.commitGraph=false', *args],
                                   cwd=ROOT, text=True).strip()


checks = []
for module, filename in [('WindowStateShift', 'proof-audit.json'),
                         ('PotentialRangeObstruction', 'potential-obstruction-proof.json')]:
    receipt = read(M74 / 'data' / filename)
    assert receipt['exit_code'] == 0 and receipt['status'].startswith('PASS_')
    for relative, field in [(f'lean/{module}.lean', 'source_sha256'),
                            (f'build/{module}.olean', 'olean_sha256'),
                            (f'logs/{module}.log', 'log_sha256')]:
        assert sha(M74 / relative) == receipt[field]
    for row in receipt['theorem_audits']:
        assert set(row['axioms']) <= {'propext', 'Classical.choice', 'Quot.sound'}
    checks.extend(receipt['theorem_audits'])
assert len(checks) == 5
interface = read(M74 / 'data/interface-audit.json')
for row in interface['current_sources']:
    assert sha(ROOT / row['path']) == row['sha256']
for row in interface['inherited_receipts']:
    assert sha(ROOT / row['path']) == row['sha256']
verification = read(M74 / 'optimization/data/verification.json')
assert verification['status'] == 'PASS_EXACT_GRAPH_WITNESSES'
assert sha(M74 / 'optimization/data/catalogue-tests.json') == verification['input_sha256']
assert sha(M74 / 'optimization/catalogue_test.py') == verification['verifier_sha256']
partial = read(M73 / 'cases/case7305/data/pending-checkpoint.json')
assert partial['status'] == 'SEMANTICS_CHECKED_REFUTATION_REPLAY_PENDING'
assert len(partial['compiled_modules']) == 92
for row in partial['archives']:
    assert sha(M73 / 'cases/case7305' / row['path']) == row['sha256']
catalogue = read(M73 / 'data/checkpoint.json')
assert catalogue['completed_cases'] == [7300, 7304, 7306]
assert catalogue['unconditional_edge_interval'] == [191, 235]

paper = ROOT / 'paper/snake9_research.tex'
mirror = Path('D:/Codex/2026-10-13/new-chat/outputs/snake9_research.tex')
assert sha(paper) == sha(mirror) == 'd422a0b3dea2c2e81cb2d63294c14ff37b2237447faf5fca193ee2664951d341'
command = "@(Get-CimInstance Win32_Process | Where-Object { $_.Name -match '^(lean|lake)(\\.exe)?$' } | Select-Object ProcessId,Name) | ConvertTo-Json -Compress"
processes = subprocess.check_output(['powershell', '-NoProfile', '-Command', command], text=True).strip()
live = json.loads(processes) if processes else []
assert not live, 'Checkpoint expects no remaining Lean/lake job'
refs = {}
for line in git('for-each-ref', '--format=%(refname:short) %(objectname)', 'refs/remotes/origin').splitlines():
    ref, revision = line.split()
    refs[ref] = revision
out = dict(status='RESEARCH_CHECKPOINT_SAVED_EXACT_OPTIMUM_UNRESOLVED',
           recorded_at=datetime.datetime.now(datetime.timezone.utc).isoformat(),
           preceding_commit=git('rev-parse', 'HEAD'), fetched_remote_refs=refs,
           edge_interval=[191, 235], upper_bound_evidence='Inspected contributor235 theorem and saved audit; no fresh full rebuild here',
           conditional_target=234, completed_stronger_share_cases=catalogue['completed_cases'],
           pending_stronger_share_cases=[7301, 7302, 7303, 7305, 7307, 7308],
           new_lean_theorem_audits=checks, exact_graph_witness_tests=6,
           pending_case7305=dict(checked_modules=92, saved_sources=len(partial['source_sha256']),
                                status=partial['status'], selected_lrat_sha256=partial['selected_lrat_sha256']),
           manuscript=dict(revision=66, next_planned_rewrite=76, sha256=sha(paper),
                           source=str(paper), editor_source=str(mirror), edited_this_round=False),
           active_lean_processes=live,
           remaining=['Six local target share certificates',
                      'Exact arbitrary-snake history graph interpretation',
                      'Full graph potential replay in Lean',
                      'No construction above191 or exact optimum'],
           scope='Saved local research and handover. Numeric graph witnesses are Python-checked; general obstruction algebra and shift identities are Lean-checked against reused support. No new unconditional bound.')
(HERE / 'checkpoint.json').write_text(json.dumps(out, indent=2)+'\n')

paths = set()
for base in [HERE, M74]:
    for p in base.rglob('*'):
        if p.is_file() and not {'build', '__pycache__'} & set(p.relative_to(base).parts):
            if p.name not in ['file-manifest.json', 'staged-evidence.json']:
                paths.add(p)
for rel in ['data/checkpoint.json', 'data/integration-audit.json', 'data/proved-model.json',
            'data/assumed-012310x12-model.json', 'data/required-shares.json',
            'cases/case7305/data/pending-checkpoint.json', 'cases/case7305/data/lrat-slice-selection.json',
            'cases/case7305/data/pending-lean-sources.tar.gz',
            'cases/case7305/data/pending-compact-proof.tar.gz',
            'cases/case7305/data/original-proof-evidence.tar.gz',
            'scripts/slice_lrat.py', 'scripts/checkpoint_pending.py']:
    paths.add(M73 / rel)
paths.update([paper, ROOT/'README.md', ROOT/'COLLABORATION.md', ROOT/'RESEARCH_LEDGER.md', ROOT/'milestones/README.md',
              ROOT/'milestones/51-exact-bucket-pressure/data/repository-check.json'])
rows = [dict(path=p.relative_to(ROOT).as_posix(), bytes=p.stat().st_size, sha256=sha(p))
        for p in sorted(paths)]
manifest = dict(status='HASHED_LOCAL_HANDOVER_EVIDENCE', files=rows,
                scope='Key handover and current-round evidence; not a full repository backup. Source/proof archives include their own complete member manifests; inherited compiled caches and unrelated local work are excluded.')
(HERE / 'file-manifest.json').write_text(json.dumps(manifest, indent=2)+'\n')
print(out['status'], len(rows), 'manifested files; no active Lean/lake processes.')
