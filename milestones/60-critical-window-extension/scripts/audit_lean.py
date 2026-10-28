from pathlib import Path
import hashlib,json,re
HERE=Path(__file__).resolve().parents[1]
record=json.loads((HERE/'logs/build-record.json').read_text())
sources={p.stem:p for p in (HERE/'lean').glob('*.lean')}
assert len(sources)==5 and set(sources)=={r['module'] for r in record['records']}
audits=[];shares=[];controls=[]
for r in record['records']:
    p=sources[r['module']]
    assert r['exit_code']==0 and hashlib.sha256(p.read_bytes()).hexdigest()==r['source_sha256']
    assert (Path(record['build'])/(r['module']+'.olean')).exists()
    log=(HERE/'logs'/(r['module']+'.log')).read_text()
    assert 'error:' not in log and 'sorryAx' not in log
    entries=re.findall(r"'([^']+)' depends on axioms: \[([^]]*)\]",log)
    entries += [(n,'') for n in re.findall(r"'([^']+)' does not depend on any axioms",log)]
    assert len(entries)==p.read_text().count('#print axioms')
    for name,text in entries:
        axioms={a.strip() for a in text.split(',') if a.strip()}
        assert axioms<={'propext','Classical.choice','Quot.sound'}
        m=re.search(r'\.T(\d+)\.in_snake$',name)
        if m:shares.append(int(m.group(1)))
        m=re.search(r'\.F(\d+)\.impossible$',name)
        if m:controls.append(int(m.group(1)))
        audits.append(dict(theorem=name,axioms=sorted(axioms)))
assert sorted(shares)==list(range(20)) and sorted(controls)==[14,15,16]
assert len(audits)==137
out=dict(status='PASS',modules=5,audits=len(audits),share_instances=shares,validity_controls=controls,
         records=record['records'],dependencies=audits,
         scope='Arbitrary-length share transport, twenty ten-transition share instances, three forbidden eleven-transition windows and conditional budget arithmetic. The cycle-to-window association is separately checked finite enumeration; no full ten-transition model or global upper-bound improvement.')
(HERE/'data/lean-audit.json').write_text(json.dumps(out,indent=2)+'\n');print({k:v for k,v in out.items() if k not in ['records','dependencies']})
