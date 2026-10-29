"""Audit only completed records; never imply the full replay has passed."""
from pathlib import Path
import json,hashlib,re,datetime
HERE=Path(__file__).resolve().parents[1]
record=json.loads((HERE/'logs/build-record.json').read_text());audits=[];modules=[]
for r in record['records']:
    if r['exit_code']!=0:continue
    src=HERE/'lean'/(r['module']+'.lean')
    assert hashlib.sha256(src.read_bytes()).hexdigest()==r['source_sha256']
    assert (Path(record['build'])/(r['module']+'.olean')).exists()
    log=(HERE/'logs'/(r['module']+'.log')).read_text()
    assert 'sorryAx' not in log and 'error:' not in log
    entries=re.findall(r"'([^']+)' depends on axioms: \[([^]]*)\]",log)
    entries += [(n,'') for n in re.findall(r"'([^']+)' does not depend on any axioms",log)]
    assert len(entries)==src.read_text(encoding='utf-8').count('#print axioms')
    for name,ax in entries:
        axioms={a.strip() for a in ax.split(',') if a.strip()}
        assert axioms<={'propext','Classical.choice','Quot.sound'}
        audits.append(dict(theorem=name,axioms=sorted(axioms)))
    modules.append(r['module'])
out=dict(status='PARTIAL_PASS',checked_at=datetime.datetime.now().astimezone().isoformat(),modules=modules,audits=audits,
    scope='Only the listed completed modules have passed. Remaining certificates are pending; no complete milestone or stronger checked graph minimum is claimed.')
(HERE/'data/partial-lean-audit.json').write_text(json.dumps(out,indent=2)+'\n')
print('Completed modules',modules,'audits',len(audits))
