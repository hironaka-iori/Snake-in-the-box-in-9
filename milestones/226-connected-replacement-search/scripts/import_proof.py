"""Copy accepted dependency artifacts without modifying their receipts."""
from pathlib import Path
import hashlib,json,re,sys
H=Path(__file__).resolve().parents[1];R=H.parents[1]
folders=['209-slice-capacity','221-square-parity','214-parity-partner-capacity','206-four-history','196-quotient-cycle-cuts','188-dimensional-constructions']
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
seen=set()
def copy(name):
    if name=='Std' or name in seen:return
    seen.add(name)
    candidates=[R/'milestones'/f/'data'/(name+'-audit.json') for f in folders]
    receipt=next((p for p in candidates if p.exists()),None)
    assert receipt is not None,name
    d=json.loads(receipt.read_bytes());assert d['status']=='PASS'
    src=Path(d['source']);obj=Path(d['object'])
    assert sha(src)==d['source_sha256'] and sha(obj)==d['olean_sha256']
    assert sha(d['log'])==d['log_sha256']
    for p,h in d['dependencies'].items():assert sha(p)==h,p
    for dep in re.findall(r'^import (\w+)$',src.read_text(encoding='utf-8'),re.M):copy(dep)
    for target,source in [(H/'lean'/(name+'.lean'),src),(H/'build'/(name+'.olean'),obj),(H/'data'/(name+'-audit.json'),receipt)]:
        if target.exists():assert target.read_bytes()==source.read_bytes()
        else:target.write_bytes(source.read_bytes())
for name in sys.argv[1:]:copy(name)
print('IMPORTED_ACCEPTED_DEPENDENCIES',len(seen))
