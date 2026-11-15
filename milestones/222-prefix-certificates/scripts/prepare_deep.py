from pathlib import Path
import hashlib,json
H=Path(__file__).resolve().parents[1]
s=(H/'scripts/prefix_search.py').read_text(encoding='utf-8')
start=s.index("folder=H/'data/cases'");end=s.index('\ndef candidates',start)
digest=hashlib.sha256((H/'data/continuation-ledger.json').read_bytes()).hexdigest()
s=s[:start]+"""folder=H/'data/deep-cases';assert not folder.exists();folder.mkdir()
assert sha(H/'data/continuation-ledger.json')==%r
ledger=json.loads((H/'data/continuation-ledger.json').read_bytes())
ledger['maximum_prefix_edges']=8
assert not ledger['queue']
"""%digest+s[end:]
marker='start=time.monotonic()\nwhile ledger'
expansion="""pending=[(k,n) for k,n in ledger['nodes'].items() if n['status']=='PENDING_DEPTH_LIMIT']
assert len(pending)==1
for k,n in pending:
 children=candidates(n['prefix']);assert children
 n.update(status='EXPANDED',next_vertices=children,children=[key(n['prefix']+[v]) for v in children])
 for v,c in zip(children,n['children']):
  assert c not in ledger['nodes'];ledger['nodes'][c]={'prefix':n['prefix']+[v],'parent':k,'status':'PENDING'};ledger['queue'].append(c)
start=time.monotonic()
while ledger"""
assert s.count(marker)==1;s=s.replace(marker,expansion)
s=s.replace("save(H/'data/prefix-ledger.json'","save(H/'data/deep-ledger.json'").replace("'ledger_sha256':sha(H/'data/prefix-ledger.json')","'ledger_sha256':sha(H/'data/deep-ledger.json')").replace("save(H/'data/prefix-summary.json'","save(H/'data/deep-summary.json'").replace('range(1,5)','range(1,9)')
(H/'scripts/prefix_deep.py').write_text(s,encoding='utf-8',newline='\n')
r=(H/'scripts/run_prefix.py').read_text(encoding='utf-8').replace('prefix_search.py','prefix_deep.py').replace('prefix-execution','deep-execution').replace('prefix-stdout','deep-stdout').replace('prefix-stderr','deep-stderr').replace('prefix-summary','deep-summary')
r=r.replace("P/'data/first-audit.json']","P/'data/first-audit.json',H/'data/continuation-ledger.json']")
(H/'scripts/run_deep.py').write_text(r,encoding='utf-8',newline='\n')
print('PREPARED_DEPTH8_CONTINUATION')
