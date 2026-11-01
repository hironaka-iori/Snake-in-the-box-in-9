"""Audit the generic canonical share adapter and the exact reused inputs."""
from pathlib import Path
import hashlib,json,re
HERE=Path(__file__).resolve().parents[1];ROOT=HERE.parents[2]
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
read=lambda p:json.loads(p.read_text())
records=read(HERE/'logs/build-record.json');support=read(HERE/'data/support.json')
assert [r['module'] for r in records]==['CanonicalShareAdapter','ConditionalCatalogueDispatch']
for prefix in ['normalization','share','coverage']:
    assert sha(Path(support[prefix+'_receipt_path']))==support[prefix+'_receipt_sha256']
for r in support['modules']:
    pinned=HERE/'upstream'/(r['module']+'.lean')
    assert sha(pinned)==r['source_sha256']
    assert sha(Path(r['olean_path']))==r['olean_sha256']
    assert sha(Path(r['inherited_log_path']))==r['inherited_log_sha256']
    assert pinned.read_bytes().replace(b'\r\n',b'\n')==(ROOT/r['source_path']).read_bytes().replace(b'\r\n',b'\n')
    assert not re.search(r'\b(sorry|admit|native_decide)\b',pinned.read_text())
checks=[];modules=[]
for record,expected_count in zip(records,[4,6]):
    source=HERE/'lean'/(record['module']+'.lean');text=source.read_text()
    log=HERE/'logs'/(record['module']+'.log');logtext=log.read_text()
    assert record['exit_code']==0
    assert record['source_sha256']==sha(source)
    assert record['support_record_sha256']==sha(HERE/'data/support.json')
    assert record['olean_sha256']==sha(HERE/'build'/(record['module']+'.olean'))
    assert not re.search(r'\b(sorry|admit|native_decide)\b',text)
    assert all(x not in logtext for x in ['error:','sorryAx','failed to delete'])
    rows=re.findall(r"'([^']+)' depends on axioms:\s*\[([^]]*)\]",logtext,re.S)+[(n,'') for n in re.findall(r"'([^']+)' does not depend on any axioms",logtext)]
    assert len(rows)==len(re.findall(r'^#print axioms ',text,re.M))==expected_count
    for name,axioms in rows:
        axs=re.findall(r'[A-Za-z][\w.]*',axioms)
        assert set(axs)<={'propext','Classical.choice','Quot.sound'}
        checks.append(dict(theorem=name,axioms=axs))
    modules.append(dict(module=record['module'],source_sha256=sha(source),olean_sha256=record['olean_sha256'],log_sha256=sha(log),theorem_count=len(rows)))
dispatch=(HERE/'logs/ConditionalCatalogueDispatch.log').read_text()
for label in ['012031','012032','012034','012301','012304','012310','012314','012340','012345']:
    cap=19 if label=='012034' else 11 if label=='012310' else 15
    premise='RefutedShare (winOf ['+', '.join(label)+']) broadBounds 12 '+str(cap)+' →'
    assert dispatch.count(premise)==2, 'Both printed catalogue theorem types must retain all nine premises'
out=dict(status='PASS_CONDITIONAL_CATALOGUE_DISPATCH',generic_adapter_status='PASS_GENERIC_CANONICAL_SHARE_ADAPTER',modules=modules,support_record_sha256=sha(HERE/'data/support.json'),theorem_audits=checks,
    generic_theorem_hypotheses=['p : Snake m','r+6 <= m','canon(dsOf p r 6) = cs or canon(reverse(dsOf p r 6)) = cs','RefutedShare (winOf cs) (replicate 5 (0,21)) 12 K'],
    generic_conclusion='K+1 <= sum_{i=0}^4 coreShare 12 p (r+i+1)',
    selected_caps={'012031':15,'012032':15,'012034':19,'012301':15,'012304':15,'012310':11,'012314':15,'012340':15,'012345':15},
    lookup='Use canon(dsOf p r 6) when it belongs to representatives; otherwise use canon(reverse(dsOf p r 6)); return selectedCap+1.',
    catalogue_hypotheses='All nine explicitly printed RefutedShare premises with the selected caps, plus p : Snake m and r+6 <= m.',
    catalogue_conclusion='windowLower p r <= sum_{i=0}^4 coreShare 12 p (r+i+1); windowLower p r >= 12; hence the share sum is at least 12 conditional on all nine certificates.',
    scope='Fresh Lean 4.19.0 checks of the generic actual-window adapter and conditional catalogue dispatch. The nine certificate premises remain explicit; no individual certificate is imported or assumed established. Existing normalization, coverage and local-share support was reused after source, receipt, artifact and log hash checks; no fresh full inherited rebuild. This does not construct a history-graph walk or establish a numerical upper bound.')
(HERE/'data/proof-audit.json').write_text(json.dumps(out,indent=2)+'\n')
print(out['status'],len(checks),'theorem audits;all nine local certificate premises explicit.',flush=True)
