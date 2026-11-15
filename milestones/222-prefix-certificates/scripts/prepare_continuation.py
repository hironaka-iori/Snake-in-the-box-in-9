from pathlib import Path
import hashlib,json
H=Path(__file__).resolve().parents[1]
s=(H/'scripts/prefix_search.py').read_text(encoding='utf-8')
start=s.index("folder=H/'data/cases'");end=s.index('\ndef candidates',start)
digest=hashlib.sha256((H/'data/prefix-ledger.json').read_bytes()).hexdigest()
replacement="""folder=H/'data/continuation-cases';assert not folder.exists();folder.mkdir()
assert sha(H/'data/prefix-ledger.json')==%r
ledger=json.loads((H/'data/prefix-ledger.json').read_bytes())
initial_jobs=ledger['jobs']
"""%digest
s=s[:start]+replacement+s[end:]
s=s.replace("save(H/'data/prefix-ledger.json'","save(H/'data/continuation-ledger.json'")
s=s.replace("'ledger_sha256':sha(H/'data/prefix-ledger.json')","'ledger_sha256':sha(H/'data/continuation-ledger.json')")
s=s.replace("save(H/'data/prefix-summary.json'","save(H/'data/continuation-summary.json'")
(H/'scripts/prefix_continue.py').write_text(s,encoding='utf-8',newline='\n')
r=(H/'scripts/run_prefix.py').read_text(encoding='utf-8').replace('prefix_search.py','prefix_continue.py').replace('prefix-execution','continuation-execution').replace('prefix-stdout','continuation-stdout').replace('prefix-stderr','continuation-stderr').replace('prefix-summary','continuation-summary')
r=r.replace("P/'data/first-audit.json']","P/'data/first-audit.json',H/'data/prefix-ledger.json']")
(H/'scripts/run_continuation.py').write_text(r,encoding='utf-8',newline='\n')
(H/'data/continuation-input.json').write_text(json.dumps({'initial_ledger_sha256':digest,'initial_jobs':json.loads((H/'data/prefix-ledger.json').read_bytes())['jobs'],'reason':'Previous native child terminated after available memory fell below768MiB; completed certificates and all pending prefixes retained.'},indent=2)+'\n',encoding='utf-8')
print('PREPARED_FROZEN_LEDGER_CONTINUATION')
