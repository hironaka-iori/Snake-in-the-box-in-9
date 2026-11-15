from pathlib import Path
import collections,hashlib,json
H=Path(__file__).resolve().parents[1];p=H/'data/regions46.json';raw=json.loads(p.read_bytes())
rows=[]
for r in raw['contexts']:
    r=dict(r)
    if r['status']=='PENDING':r['status']='OPEN'
    rows.append(r)
out=dict(status='STATIC_BASELINE',width=46,contexts=rows,counts=dict(collections.Counter(r['status'] for r in rows)),pins={str(p):hashlib.sha256(p.read_bytes()).hexdigest()},scope='Only initial necessary domain conditions. No inherited smaller-width exclusion.')
(H/'data/baseline46.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')
print(out['counts'])
