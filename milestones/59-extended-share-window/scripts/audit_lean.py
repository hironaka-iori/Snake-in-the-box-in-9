"""Check complete source coverage, successful exits and theorem dependencies."""
from pathlib import Path
import hashlib,json,re
HERE=Path(__file__).resolve().parents[1]
record=json.loads((HERE/'logs/build-record.json').read_text())
sources={p.relative_to(HERE/'lean').with_suffix('').as_posix():p for p in (HERE/'lean').rglob('*.lean')}
assert len(sources)==36 and set(sources)=={r['module'] for r in record['records']}
audits=[];instances=[]
for r in record['records']:
    assert r['exit_code']==0
    source=sources[r['module']]
    assert hashlib.sha256(source.read_bytes()).hexdigest()==r['source_sha256']
    assert (Path(record['build'])/(r['module']+'.olean')).is_file()
    log=(HERE/'logs'/(r['module'].replace('/','-')+'.log')).read_text()
    assert 'error:' not in log and 'sorryAx' not in log
    entries=re.findall(r"'([^']+)' depends on axioms: \[([^]]*)\]",log)
    entries += [(n,'') for n in re.findall(r"'([^']+)' does not depend on any axioms",log)]
    assert len(entries)==source.read_text().count('#print axioms')
    for name,text in entries:
        axioms={x.strip() for x in text.split(',') if x.strip()}
        assert axioms<={'propext','Classical.choice','Quot.sound'}
        match=re.search(r'\.G(\d+)\.in_snake$',name)
        if match:instances.append(int(match.group(1)))
        if re.search(r'\.G\d+\.',name) and not match:assert axioms<={'propext'}
        audits.append(dict(theorem=name,axioms=sorted(axioms)))
rows=json.loads((HERE/'data/geometry.json').read_text())['patterns']
assert sorted(instances)==[i for i,r in enumerate(rows) if r['share_lower']>0]
assert len(instances)==357
out=dict(status='PASS',modules=len(sources),audits=len(audits),arbitrary_snake_instances=len(instances),
         records=record['records'],dependencies=audits,
         scope='All 357 positive geometric window inequalities in arbitrary snakes, fivefold share overlap, and conditional extended-window boundary arithmetic. Inherited numerical model premises and full graph-to-snake assembly remain unresolved.')
(HERE/'data/lean-audit.json').write_text(json.dumps(out,indent=2)+'\n')
print({k:v for k,v in out.items() if k not in ['records','dependencies']})
