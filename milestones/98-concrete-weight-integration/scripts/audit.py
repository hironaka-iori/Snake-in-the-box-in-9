"""Audit completed weight proofs, literal rules, and exact dependency receipts."""
from pathlib import Path
import ast,hashlib,json,re
HERE=Path(__file__).resolve().parents[1];ROOT=HERE.parents[1]
read=lambda p:json.loads(p.read_text(encoding='utf-8-sig'))
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
env=read(HERE/'data/environment.json')
assert 'overlay' in env
for path,digest in env['receipts'].items():assert sha(ROOT/path)==digest,path
for path,digest in env['sources'].items():assert sha(ROOT/path)==digest,path
for item in read(HERE/'data/additional-root-objects.json'):
    assert sha(ROOT/item['source'])==item['source_sha256']
    assert sha(ROOT/item['original'])==sha(ROOT/item['copy'])==item['object_sha256']
for p in env['ports']:
    assert sha(ROOT/p['original'])==sha(ROOT/p['source'])==p['sha256']
rules=read(HERE/'data/conditioned-rules.json')
expected=[([0,1,2,3,1,4],[3,3,3,6,5],48),([0,1,2,3,4,5],[3,6,2,3,6],96),
          ([0,1,2,0,3,4],[6,3,6,3,3],96),([0,1,2,3,4,5],[4,6,2,3,6],96),
          ([0,1,2,3,4,5],[4,5,4,2,6],120)]
assert [(r['directions'],r['symbols'],r['credit']) for r in rules]==expected
text=(HERE/'lean/CountConditionedCredits98.lean').read_text()
body=text.split('def conditionedCredit',1)[1].split('theorem actual_conditioned_credit',1)[0]
actual=[(ast.literal_eval(a),ast.literal_eval(b),int(c)+1) for a,b,c in
        re.findall(r'ruleCredit (\[[^]]+\]) (\[[^]]+\]) (\d+) di code',body)]
assert actual==expected
assert 'code % 7776 = encodeCounts syms.reverse 0' in text
assert 'canon (((extensions.getD di []).drop 3).reverse) = cs' in text
cf=(HERE/'lean/CountFreeCredits98.lean').read_text()
def floors(name,nextname):
    s=cf.split('def '+name,1)[1].split('def '+nextname,1)[0]
    return {''.join(str(x) for x in ast.literal_eval(a)):int(b)
            for a,b in re.findall(r'if cs = (\[[^]]+\]) then (\d+)',s)}
completed=floors('completedFloor','conditionalFloor')
conditional=floors('conditionalFloor','completedCredit')
assert completed=={'012031':16,'012304':16,'012310':12,'012314':16,'012345':12}
assert conditional=={'012032':16,'012034':18,'012301':16,'012340':16,'012345':16}
checked=[]
for src in sorted((HERE/'lean').glob('*.lean')):
    receipt=HERE/'data'/(src.stem+'-audit.json');r=read(receipt)
    assert r['status']=='PASS_CONCRETE_WEIGHT_MODULE' and r['exit_code']==0
    assert sha(src)==r['source_sha256']==sha(HERE/r['source_snapshot'])
    assert sha(HERE/'build'/(src.stem+'.olean'))==r['olean_sha256']
    assert sha(HERE/r['log'])==r['log_sha256']
    assert sha((HERE/r['source_snapshot']).parent/'checker.py.txt')==r['checker_sha256']
    for path,digest in r['dependencies'].items():assert sha(ROOT/path)==digest,path
    assert src.read_text().count('#print axioms')==len(r['theorem_audits'])
    assert all(set(t['axioms'])<={'propext','Classical.choice','Quot.sound'} for t in r['theorem_audits'])
    checked.append(dict(module=src.stem,receipt=receipt.relative_to(ROOT).as_posix(),receipt_sha256=sha(receipt),theorem_audits=len(r['theorem_audits'])))
numeric=read(HERE/'data/weight-model-audit.json')
assert numeric['status']=='PASS_INDEPENDENT_SAVED_KEY_WEIGHT_RECONSTRUCTION'
assert numeric['edges']==4947008 and numeric['contexts']==791
assert numeric['script_sha256']==sha(HERE/'scripts/audit_weight_model.py')
for path,digest in numeric['source_files_sha256'].items():assert sha(ROOT/path)==digest,path
result=dict(status='PASS_COMPLETE_WEIGHT_AND_CONDITIONAL_BOUND_ASSEMBLY',modules=checked,
    theorem_audits=sum(r['theorem_audits'] for r in checked),
    conditioned_rules=expected,completed_floors=completed,conditional_additions=conditional,
    environment_sha256=sha(HERE/'data/environment.json'),weight_model_audit_sha256=sha(HERE/'data/weight-model-audit.json'),
    exact_ports_preserved=True,scope='Actual edge-weight and global charge bounds checked. Actual full-key walk and numerical upper-bound assembly retain two reference-catalogue premises. Conditional234 also retains five local refutations. Concrete potential/range certificates on the defined graph remain unproved here.')
(HERE/'data/proof-summary.json').write_text(json.dumps(result,indent=2)+'\n')
print(result['status'],len(checked),'modules;',result['theorem_audits'],'audits')
