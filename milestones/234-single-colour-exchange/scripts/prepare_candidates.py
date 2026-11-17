from pathlib import Path
import hashlib,json
H=Path(__file__).resolve().parents[1];P=H.parent/'232-minority-contraction'
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
source=H/'data/exchange.json';d=json.loads(source.read_bytes());receipt=H/'data/exchange-execution.json';e=json.loads(receipt.read_bytes())
assert e['status']=='ACCEPTED_NATIVE_RESULT' and sha(source)==e['result_sha256']
assert d['status']=='COMPLETE_STATIC_COVER' and d['descriptions']==2227200
basepath=H/'data/bases.json';bases={b['id']:set(b['vertices']) for b in json.loads(basepath.read_bytes())['bases']}
groups={}
for x in d['candidates']:
 U=bases[x['base']];assert x['removed'] in U and x['added'] not in U
 V=tuple(sorted((U-{x['removed']})|{x['added']}));assert len(V)==96
 groups.setdefault(V,[]).append(x)
out=dict(bases=[dict(id=i,vertices=list(v),descriptions=xs) for i,(v,xs) in enumerate(groups.items())],pins={str(p):sha(p) for p in [source,receipt,basepath,H/'data/exchange-decisions.bin']},scope='Distinct surviving minority classes after exact equality deduplication. Static exclusions remain independently auditable; no Hamiltonian exclusion is inferred from survival.')
(H/'data/candidates.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')
s=(P/'scripts/minority.py').read_text().replace("H/'data/bases.json'","H/'data/candidates.json'")
(H/'scripts/hamilton.py').write_text(s,encoding='utf-8')
s=(H/'scripts/run_exchange.py').read_text().replace('exchange.py','hamilton.py').replace("H/'data/bases.json'","H/'data/candidates.json'")
(H/'scripts/run_hamilton.py').write_text(s,encoding='utf-8')
print('CANDIDATE_DESCRIPTIONS',len(d['candidates']),'DISTINCT_CLASSES',len(groups))
