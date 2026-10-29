from pathlib import Path
import hashlib,itertools,json,re
HERE=Path(__file__).resolve().parents[1]
record=json.loads((HERE/'logs/build-record.json').read_text());build=Path(record['build']);out=[]
for r in record['records']:
    if not r['module'].startswith('CountPhase'):continue
    name=r['module'];source=HERE/f'lean/{name}.lean';s=source.read_text(encoding='utf-8')
    assert r['exit_code']==0 and hashlib.sha256(source.read_bytes()).hexdigest()==r['source_sha256']
    assert (build/f'{name}.olean').exists() and not re.search(r'\b(sorry|admit|native_decide)\b',s)
    log=(HERE/f'logs/{name}.log').read_text(encoding='utf-8');assert 'error:' not in log and 'sorryAx' not in log
    audits=re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]",log,re.S)
    assert len(audits)==5
    assert all(set(re.findall(r'[A-Za-z][\w.]*',a))<={'propext','Classical.choice','Quot.sound'} for _,a in audits)
    out.append(dict(module=name,checks=5,source_sha256=r['source_sha256']))
NB=[{v^(1<<d) for d in range(9)} for v in range(512)]
for r in json.loads((HERE/'data/new-count-certificates.json').read_text()):
    W=[0]
    for d in r['directions']:W.append(W[-1]^(1<<d))
    j=r['position'];assert W[j]==r['vertex'];T=set(W);D=set(r['forced_corners'])
    free=set(range(9))-{r['directions'][j-1],r['directions'][j]}
    K={W[j]^(1<<a)^(1<<b) for a,b in itertools.combinations(free,2)}
    assert len(D)==3 and D<=K
    assert all(any(len(NB[v]&(T|{q}))>2 for v in T|{q}) for q in D)
assert len(out)==2
data=dict(status='PASS',modules=2,theorem_audits=10,records=out,
    scope='Two arbitrary-snake singleton lower bounds three and their direct finite corner witnesses; no full-model bridge.')
(HERE/'data/count-lean-audit.json').write_text(json.dumps(data,indent=2)+'\n');print(data)
