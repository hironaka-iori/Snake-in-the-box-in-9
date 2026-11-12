from pathlib import Path
H=Path(__file__).resolve().parents[1]
source=(H/'scripts/retry_solver.py').read_text()
old="bank=json.loads((H/'data/bank9-input.json').read_text())"
new="bankraw=(H/'data/bank9-input.json').read_bytes();bankhash=hashlib.sha256(bankraw).hexdigest()\nassert bankhash==previous['bank_sha256']\nbank=json.loads(bankraw)"
assert source.count(old)==1
source=source.replace(old,new)
source=source.replace("source_sha256=hashlib.sha256(source.read_bytes()).hexdigest(),script_sha256=", "bank_sha256=bankhash,source_sha256=hashlib.sha256(source.read_bytes()).hexdigest(),script_sha256=")
target=H/'scripts/retry_solver_pinned.py';assert not target.exists();target.write_text(source,encoding='utf-8',newline='\n')
print('PREPARED_PINNED_RETRY')
