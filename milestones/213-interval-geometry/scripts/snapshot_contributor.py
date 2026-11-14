"""Save the exact inspected contributor theorem and assembly records."""
from pathlib import Path
import hashlib,json,re,subprocess
H=Path(__file__).resolve().parents[1];R=H.parents[1]
revision='b0521e1d14fd52c62db4cdeccc356b70a623eb82'
report=(H/'logs/contributor233-review.md').read_text(encoding='utf-8')
rows=re.findall(r'\| `([^`]+)` \| `([0-9a-f]{64})` \|',report)
assert len(rows)==11
saved=[]
for name,expected in rows:
    data=subprocess.check_output(['git','-c','core.commitGraph=false','-c','maintenance.auto=false','-c','gc.auto=0','show',revision+':'+name],cwd=R)
    digest=hashlib.sha256(data).hexdigest();assert digest==expected
    destination=H/'data/contributor233'/name;destination.parent.mkdir(parents=True,exist_ok=True);destination.write_bytes(data)
    saved.append({'source_path':name,'snapshot':str(destination.relative_to(H)),'sha256':digest,'bytes':len(data)})
record={'revision':revision,'audit_revision':'b65d30ca15441420b8f4538f671e589c2502674f','files':saved,'review_sha256':hashlib.sha256((H/'logs/contributor233-review.md').read_bytes()).hexdigest(),'status':'COMPLETED_CONTRIBUTOR_THEOREM_WITH_SAVED_ASSEMBLY_AUDIT','independent_full_rebuild':False,'branch_merged':False}
(H/'data/contributor233-review.json').write_text(json.dumps(record,indent=2)+'\n')
print('SNAPSHOT_CONTRIBUTOR233',len(saved),'pinned files')
