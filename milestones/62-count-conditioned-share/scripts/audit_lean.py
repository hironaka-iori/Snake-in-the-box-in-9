from pathlib import Path
import json,hashlib,re
HERE=Path(__file__).resolve().parents[1]
record=json.loads((HERE/'logs/build-record.json').read_text());sources={p.stem:p for p in (HERE/'lean').glob('*.lean')}
assert len(sources)==12 and set(sources)=={r['module'] for r in record['records']}
audits=[];local=[];graphs=[]
for r in record['records']:
    src=sources[r['module']];text=src.read_text(encoding='utf-8')
    assert r['exit_code']==0 and hashlib.sha256(src.read_bytes()).hexdigest()==r['source_sha256']
    assert (Path(record['build'])/(r['module']+'.olean')).exists()
    assert not re.search(r'\b(sorry|admit|axiom)\b',text)
    log=(HERE/'logs'/(r['module']+'.log')).read_text()
    assert 'error:' not in log and 'sorryAx' not in log
    entries=re.findall(r"'([^']+)' depends on axioms: \[([^]]*)\]",log)
    entries += [(n,'') for n in re.findall(r"'([^']+)' does not depend on any axioms",log)]
    assert len(entries)==text.count('#print axioms')
    for name,ax in entries:
        axioms={a.strip() for a in ax.split(',') if a.strip()};assert axioms<={'propext','Classical.choice','Quot.sound'}
        if name.endswith('.in_snake'):local.append(name)
        if name.endswith('.every_closed_walk'):graphs.append(name)
        audits.append(dict(theorem=name,axioms=sorted(axioms)))
assert len(local)==8 and len(graphs)==3 and len(audits)==88
out=dict(status='PASS',modules=12,audits=88,arbitrary_snake_bounds=8,closed_walk_certificates=3,
    scope='Eight unconditional local geometric improvements and three restricted finite graph minima. Count-based and floating LP candidates excluded. No new global bound.',
    records=record['records'],dependencies=audits)
(HERE/'data/lean-audit.json').write_text(json.dumps(out,indent=2)+'\n');print({k:v for k,v in out.items() if k not in ['records','dependencies']})
