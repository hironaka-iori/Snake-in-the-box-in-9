"""Prepare a matched pair differing only in the final natural comparison."""
from pathlib import Path
import hashlib,json
HERE=Path(__file__).resolve().parents[1]
p=HERE/'lean/CompletedBlock102D99Q37.lean';source=p.read_text(encoding='utf-8')
test=source.split('checkPrefix ',1)[1].split(' 6 0 1807',1)[0]
assert source.count(test)==2
ble='''(fun code => Nat.ble
      (483+min 551 (value Completed.n5_57 (code%7776)))
      (120*(code%6+1)+max (if digit code 1 ≤ 2 ∧ digit code 2 ≤ 2 then 19 else 18) (if code%7776 = 3221 then 96 else 0)+min 551 (value Completed.n5_19 (code/6))))'''
rows=[]
for kind in ['Decide','Ble']:
    s='import NatBoolean102\n'+source.replace('Snake9.PrefixCertificates102',f'Snake9.BooleanComparison102.{kind}')
    if kind=='Ble':
        s=s.replace(test,ble).replace('simp only [completed_simplified_99_37,','simp only [Snake9.BooleanComparison102.ble_decide, completed_simplified_99_37,')
    name='Controlled'+kind+'102';out=HERE/'lean'/(name+'.lean')
    if out.exists() and out.read_text(encoding='utf-8')==s:pass
    else:
        assert not (HERE/'data'/(name+'-audit.json')).exists()
        out.write_text(s,encoding='utf-8')
    rows.append(dict(module=name,kind=kind,source_sha256=hashlib.sha256(out.read_bytes()).hexdigest()))
(HERE/'data/boolean-comparison-candidates.json').write_text(json.dumps(dict(
    status='PREPARED_NOT_TIMED',original_source_sha256=hashlib.sha256(p.read_bytes()).hexdigest(),
    context=[99,37],profile='completed',variants=rows,
    scope='Same potential trees, weight, accepted codes, prefix recursion, imports and bounded transfer. Only the leaf comparison and its equality rewrite differ.'),indent=2)+'\n')
print('PREPARED_MATCHED_BOOLEAN_COMPARISON')
