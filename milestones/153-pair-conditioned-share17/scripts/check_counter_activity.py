"""Check whether apparently unused lower bounds also have unused registers."""
from pathlib import Path
from collections import Counter
import gzip,hashlib,json
H=Path(__file__).resolve().parents[1];P=H/'critical/work/critical17'
read=lambda p:json.loads(p.read_text(encoding='utf-8-sig'))
meta=json.loads(gzip.decompress((P/'meanings.json.gz').read_bytes()))
core=set()
for line in (P/'core.cnf').read_text().splitlines():
    if line and line[0] not in 'pc':core.update(abs(int(x)) for x in line.split() if x!='0')
derived=set(read(H/'data/proof-variables.json'))
rows=[]
for ci,(lits,cap,kind) in enumerate(meta['ctrs']):
    vs={int(v) for v,m in meta['meaning'].items() if m[0]=='r' and m[1]==ci}
    rows.append(dict(counter=ci,kind=kind,register_variables=len(vs),core_registers=len(vs&core),derived_registers=len(vs&derived)))
out=dict(status='PASS_COUNTER_REGISTER_ACTIVITY_INSPECTION',rows=rows,
    no_weakening_claimed=True,source_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest())
target=H/'data/counter-activity.json';assert not target.exists();target.write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')
print(json.dumps(out))
