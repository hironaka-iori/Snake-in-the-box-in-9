"""Find already saved ordinary witnesses for current critical windows."""
from pathlib import Path
import hashlib,json,sys
ROOT=Path(__file__).resolve().parents[3];HERE=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'milestones/42-six-count-state-model/scripts'))
import model
def key(ds,cs):return min((model.canon(ds),tuple(cs)),(model.canon(ds[::-1]),tuple(cs[::-1])))
rows=json.loads((HERE/'data/windows.json').read_text());wanted={key(r['directions'],r['counts']):r for r in rows}
found={}
for folder in ['50-three-count-return','51-exact-bucket-pressure']:
 for path in (ROOT/'milestones'/folder).rglob('*.json'):
  if 'build' in path.parts:continue
  try:r=json.loads(path.read_text())
  except (UnicodeError,ValueError):continue
  if not isinstance(r,dict) or r.get('status') not in ['SAT','FEASIBLE'] or 'selected' not in r:continue
  ds=r.get('directions',r.get('dirs'));cs=r.get('counts')
  if cs is None and r.get('census'):cs=[min(a,6) for a in r['census']['alpha']]
  if ds is None or cs is None or len(ds)!=6 or len(cs)!=5:continue
  k=key(ds,cs)
  if k not in wanted:continue
  # Require the actual witness to meet the exact low-count / six-or-more buckets.
  actual=r['census']['alpha']
  if key(ds,[min(a,6) for a in actual])!=k:continue
  found.setdefault(k,dict(**wanted[k],controls=[]))['controls'].append(dict(file=path.relative_to(ROOT).as_posix(),sha256=hashlib.sha256(path.read_bytes()).hexdigest(),total_share=r['census']['total_share']))
out=sorted(found.values(),key=lambda r:-r['occurrences'])
(HERE/'data/supported-critical-windows.json').write_text(json.dumps(out,indent=2)+'\n')
print('Current critical windows with saved positive controls',len(out))
for r in out[:12]:print(r['directions'],r['counts'],'occurrences',r['occurrences'],'saved shares',[c['total_share'] for c in r['controls']])
