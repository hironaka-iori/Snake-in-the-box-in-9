"""Verify exact local proof receipts and independently audited finite data."""
from pathlib import Path
import hashlib,json,re
HERE=Path(__file__).resolve().parents[1]; ROOT=HERE.parents[1]
read=lambda p:json.loads(p.read_text(encoding='utf-8-sig'))
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
assert not (HERE/'data/check.lock').exists()
env=read(HERE/'data/environment.json')
for group in ['receipts','sources']:
    for path,digest in env[group].items(): assert sha(ROOT/path)==digest,path
checked=[]; pending=[]
for src in sorted((HERE/'lean').glob('*.lean')):
    receipt=HERE/'data'/f'{src.stem}-audit.json'
    if not receipt.exists():
        attempts=sorted((HERE/'logs').glob(f'{src.stem}-*-record.json'))
        row=dict(module=src.stem,source_sha256=sha(src),status='NOT_ATTEMPTED')
        if attempts:
            last=attempts[-1];r=read(last)
            assert r['source_sha256']==sha(src)
            row.update(status='TIMED_OUT' if r['timeout'] else 'FAILED_ATTEMPT',
                       last_attempt=last.relative_to(HERE).as_posix(),last_attempt_sha256=sha(last),
                       seconds=r['seconds'],exit_code=r['exit_code'])
        pending.append(row)
        continue
    r=read(receipt)
    assert r['status']=='PASS_DEFINED_POTENTIAL_MODULE' and r['exit_code']==0 and not r['timeout']
    assert sha(src)==r['source_sha256']==sha(HERE/r['source_snapshot'])
    assert sha(HERE/'build'/f'{src.stem}.olean')==r['olean_sha256']
    assert sha(HERE/r['log'])==r['log_sha256']
    assert sha((HERE/r['source_snapshot']).parent/'checker.py.txt')==r['checker_sha256']
    for path,digest in r['dependencies'].items(): assert sha(ROOT/path)==digest,path
    assert src.read_text().count('#print axioms')==len(r['theorem_audits'])
    assert all(set(t['axioms'])<={'propext','Classical.choice','Quot.sound'} for t in r['theorem_audits'])
    assert not re.search(r'\b(sorry|admit|native_decide)\b',src.read_text())
    checked.append(dict(module=src.stem,receipt=receipt.relative_to(ROOT).as_posix(),
        receipt_sha256=sha(receipt),theorem_audits=len(r['theorem_audits']),seconds=r['seconds']))
numeric=read(HERE/'data/defined-potential-audit.json')
assert numeric['status']=='PASS_ALL_DEFINED_GRAPH_POTENTIAL_INEQUALITIES'
assert numeric['counts']==dict(accepted=4947008,saved_intersection=4947008,extra=0,missing=0)
assert numeric['script_sha256']==sha(HERE/'scripts/audit_defined_potentials.py')
for path,digest in numeric['source_files_sha256'].items(): assert sha(ROOT/path)==digest,path
literal=read(HERE/'data/potential-literal-audit.json')
assert literal['status']=='PASS_PARSED_LEAN_POTENTIAL_LITERAL_VALUES'
assert literal['total_checked_values']==3203712
assert literal['script_sha256']==sha(HERE/'scripts/audit_potential_literals.py')
for path,digest in literal['source_files_sha256'].items(): assert sha(ROOT/path)==digest,path
reuse=read(HERE/'data/context-compression.json')
assert reuse['contexts']==791 and reuse['joint_distinct_groups']==582
assert reuse['joint_saved_context_checks']==209
assert reuse['source_audit_sha256']==sha(HERE/'data/defined-potential-audit.json')
assert reuse['script_sha256']==sha(HERE/'scripts/context_compression.py')
for path,digest in reuse['source_inputs_sha256'].items(): assert sha(ROOT/path)==digest,path
compression=read(HERE/'data/compression.json')
required=['PotentialTree99','CompletedPotential99','ConditionalPotential99','FastDiagram99',
          'PotentialChecker99','ConcreteAssembly99','PotentialPilot99','PotentialPilotLarge99']
assert set(required)<={r['module'] for r in checked}
result=dict(status='PASS_CONCRETE_POTENTIAL_RANGES_AND_FINITE_PILOTS',modules=checked,
    pending_modules=pending,theorem_audits=sum(r['theorem_audits'] for r in checked),
    numerical_defined_graph_edges=4947008,numerical_extra_rows=0,numerical_missing_rows=0,
    concrete_ranges_checked=[551,602],complete_graph_inequality_checked_in_lean=False,
    complete_context_modules=[n for n in ['CompletedContext99','ConditionalContext99'] if n in {r['module'] for r in checked}],
    environment_sha256=sha(HERE/'data/environment.json'),
    defined_potential_audit_sha256=sha(HERE/'data/defined-potential-audit.json'),
    literal_audit_sha256=sha(HERE/'data/potential-literal-audit.json'),
    context_reuse_sha256=sha(HERE/'data/context-compression.json'),
    scope='Both full defined-graph inequalities checked in Python. Concrete ranges and only the listed finite intervals and contexts checked in Lean. Full graph certificates and reference/local premises remain.')
(HERE/'data/proof-summary.json').write_text(json.dumps(result,indent=2)+'\n')
print(result['status'],len(checked),'modules',result['theorem_audits'],'theorem audits',len(pending),'pending modules')
