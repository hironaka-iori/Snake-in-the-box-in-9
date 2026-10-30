from pathlib import Path
import hashlib,json,re
HERE=Path(__file__).resolve().parents[1]
record=json.loads((HERE/'logs/build-record.json').read_text());build=Path(record['build'])
assert {r['module'] for r in record['records']}=={p.stem for p in (HERE/'lean').glob('*.lean')}
rows=[]
for r in record['records']:
    name=r['module'];source=HERE/f'lean/{name}.lean';text=source.read_text(encoding='utf-8')
    assert r['exit_code']==0 and hashlib.sha256(source.read_bytes()).hexdigest()==r['source_sha256']
    assert (build/f'{name}.olean').exists() and not re.search(r'\b(sorry|admit|native_decide)\b',text)
    log=(HERE/f'logs/{name}.log').read_text(encoding='utf-8');assert 'error:' not in log and 'sorryAx' not in log
    audits=re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]",log,re.S)
    audits += [(n,'') for n in re.findall(r"'([^']+)' does not depend on any axioms",log)]
    expected=re.findall(r'^#print axioms (\w+)',text,re.M)
    assert sorted(n.rsplit('.',1)[-1] for n,_ in audits)==sorted(expected)
    assert all(set(re.findall(r'[A-Za-z][\w.]*',a))<={'propext','Classical.choice','Quot.sound'} for _,a in audits)
    rows.append(dict(module=name,checks=len(audits),source_sha256=r['source_sha256']))
out=dict(status='PASS',modules=len(rows),theorem_audits=sum(r['checks'] for r in rows),records=rows,
    scope='Generic cover monotonicity under proved pruning, conditional bound arithmetic, and the insufficiency of mean 1492/3 for target 233. Concrete catalogues, complete graph interpretation and full potential replay are not checked in Lean here.')
(HERE/'data/lean-audit.json').write_text(json.dumps(out,indent=2)+'\n');print(out)
