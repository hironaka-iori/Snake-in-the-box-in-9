from pathlib import Path
import hashlib,json
H=Path(__file__).resolve().parents[1];R=H.parents[1]
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
out=[]
for folder,module in [('218-direct-partner','Cycle218'),('219-linear-partner','Degree219')]:
 receipt=R/'milestones'/folder/'data'/(module+'-audit.json');d=json.loads(receipt.read_bytes())
 assert d['status']=='PASS' and d['exit_code']==0 and d['stop_reason'] is None
 for pk,hk in [('source','source_sha256'),('object','olean_sha256'),('log','log_sha256')]:assert sha(d[pk])==d[hk]
 assert all(sha(p)==v for p,v in d['dependencies'].items())
 out.append(dict(module=module,receipt=str(receipt),receipt_sha256=sha(receipt),source=d['source'],source_sha256=d['source_sha256'],object=d['object'],olean_sha256=d['olean_sha256'],log=d['log'],log_sha256=d['log_sha256'],dependencies=d['dependencies'],axioms=d['axioms']))
(H/'data/prior-proof-audit.json').write_text(json.dumps(dict(status='PASS_ACCEPTED_PROOF_PINS',proofs=out,scope='Rechecked accepted source/object/log/dependency hashes; no fresh Lean compilation of these older modules.'),indent=2)+'\n',encoding='utf-8')
print('PRIOR_PROOF_PINS_PASS')
