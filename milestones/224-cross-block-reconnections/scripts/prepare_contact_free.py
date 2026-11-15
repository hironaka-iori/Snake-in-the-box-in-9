"""Remove every short-closure premise from the numerical 33-edge query."""
from pathlib import Path
import collections,hashlib,json
H=Path(__file__).resolve().parents[1]
raw=(H/'data/regions.json').read_bytes();data=json.loads(raw)
for row in data['contexts']:
    for part in row['parts']:part['rejections']=[x for x in part['rejections'] if x!='NO_CROSS_CONTACT']
    row['status']='STATIC_EXCLUDED' if any(p['rejections'] for p in row['parts']) else 'PENDING'
data['original_regions_sha256']=hashlib.sha256(raw).hexdigest()
data['scope']='All224 maximal33-edge window pairs. Only geometric static restrictions; no contact requirement and no short-move closure premise. Same fixed anchors/outside positions, endpoint24 extension and four crossings.'
p=H/'data/regions33-free.json';assert not p.exists();p.write_text(json.dumps(data,indent=2)+'\n',encoding='utf-8')
s=(H/'scripts/joint_regions.py').read_text(encoding='utf-8').replace("H/'data/regions.json'","H/'data/regions33-free.json'")
s=s.replace("        model.add(sum(x[z] for z in part['contact_candidates'])>=1)\n",'')
s=s.replace('Mutual cross-contact pruning is conditional on the native round193 short-move closure.','No contact restriction or short-move closure premise.')
(H/'scripts/joint_regions33_free.py').write_text(s,encoding='utf-8')
s=(H/'scripts/run_regions.py').read_text(encoding='utf-8').replace('scripts/joint_regions.py','scripts/joint_regions33_free.py').replace("H/'data/regions.json'","H/'data/regions33-free.json'")
(H/'scripts/run_regions33_free.py').write_text(s,encoding='utf-8')
print(json.dumps(dict(statuses=dict(collections.Counter(r['status'] for r in data['contexts'])),removed_contact_premise=True)),flush=True)
