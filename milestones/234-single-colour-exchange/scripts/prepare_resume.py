"""Prepare only still-unresolved candidate classes after a terminal native batch."""
from pathlib import Path
import hashlib,json
H=Path(__file__).resolve().parents[1]
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
receipt=H/'data/hamilton-execution.json';e=json.loads(receipt.read_bytes())
assert e['status']=='ACCEPTED_NATIVE_RESULT' and e['exit_code']==0
p=H/'data/hamilton.json';raw=json.loads(p.read_bytes());assert sha(p)==e['result_sha256'] and raw['status']!='RUNNING' and raw['witness'] is None
forced=H/'data/forced-cycles.json';fc=json.loads(forced.read_bytes());solved={r['id'] for r in raw['results'] if r['status']=='INFEASIBLE'}|{r['id'] for r in fc['rows'] if r['status']=='CERTIFICATE'}
source=H/'data/candidates.json';c=json.loads(source.read_bytes());remaining=[b for b in c['bases'] if b['id'] not in solved]
out=dict(bases=remaining,pins={str(q):sha(q) for q in [source,receipt,p,forced]},scope='Only candidates lacking either a completed native exclusion or a generated elementary certificate. Certificates must pass independent replay before final coverage is claimed.')
(H/'data/remaining.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')
s=(H/'scripts/hamilton.py').read_text().replace("H/'data/candidates.json'","H/'data/remaining.json'")
s=s.replace('    save()\nout[\'status\']','    if len(out[\'results\'])%25==0:save()\nout[\'status\']')
(H/'scripts/hamilton_resume.py').write_text(s,encoding='utf-8')
s=(H/'scripts/run_hamilton.py').read_text().replace('hamilton.py','hamilton_resume.py').replace("H/'data/candidates.json'","H/'data/remaining.json'")
(H/'scripts/run_resume.py').write_text(s,encoding='utf-8')
print('REMAINING_CLASSES',len(remaining))
