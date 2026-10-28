from pathlib import Path
import hashlib,json,re
HERE=Path(__file__).resolve().parents[1]
record=json.loads((HERE/'logs/build-record.json').read_text())
sources={p.stem:p for p in (HERE/'lean').glob('*.lean')}
assert len(sources)==21 and set(sources)=={r['module'] for r in record['records']}
audits=[];geometric=[];controls=[];graphs=[]
for r in record['records']:
    source=sources[r['module']]
    assert r['exit_code']==0 and hashlib.sha256(source.read_bytes()).hexdigest()==r['source_sha256']
    assert (Path(record['build'])/(r['module']+'.olean')).exists()
    log=(HERE/'logs'/(r['module']+'.log')).read_text()
    assert 'error:' not in log and 'sorryAx' not in log
    entries=re.findall(r"'([^']+)' depends on axioms: \[([^]]*)\]",log)
    entries += [(n,'') for n in re.findall(r"'([^']+)' does not depend on any axioms",log)]
    assert len(entries)==source.read_text().count('#print axioms')
    for name,text in entries:
        axioms={a.strip() for a in text.split(',') if a.strip()}
        assert axioms<={'propext','Classical.choice','Quot.sound'}
        m=re.search(r'FamilyShare61\.G(\d+)\.in_snake$',name)
        if m:geometric.append(int(m.group(1)))
        m=re.search(r'FamilyValidity61\.F(\d+)\.impossible$',name)
        if m:controls.append(int(m.group(1)))
        if name.endswith('.every_closed_walk'):graphs.append(name)
        audits.append(dict(theorem=name,axioms=sorted(axioms)))
rows=json.loads((HERE/'data/geometry.json').read_text())['patterns']
assert sorted(geometric)==[i for i,r in enumerate(rows) if r['lower']>0]
assert sorted(controls)==list(range(27)) and len(graphs)==4 and len(audits)==678
out=dict(status='PASS',modules=21,audits=len(audits),positive_geometric_instances=len(geometric),
         validity_controls=len(controls),finite_graph_certificates=4,records=record['records'],dependencies=audits,
         scope='Positive local share bounds for arbitrary matching snakes, forbidden cycle windows, and all-closed-walk potential bounds with attaining finite cycles. Complete source-family extraction and lift coverage are separately verified computations. No global snake bound.')
(HERE/'data/lean-audit.json').write_text(json.dumps(out,indent=2)+'\n');print({k:v for k,v in out.items() if k not in ['records','dependencies']})
