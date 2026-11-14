from pathlib import Path
import hashlib,json
H=Path(__file__).resolve().parents[1]
old='simpa only [List.mem_cons,List.mem_singleton]'
new='simpa only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false]'
for name in ['emit_cover.py','emit_cover_chunked.py']:
 p=H/'scripts'/name;s=p.read_text(encoding='utf-8');p.write_bytes(s.replace(old,new).encode('utf-8'))
changed=[]
for p in (H/'lean').glob('Partition*.lean'):
 if (H/'data'/(p.stem+'-audit.json')).exists():continue
 s=p.read_text(encoding='utf-8')
 if old in s:
  p.write_bytes(s.replace(old,new).encode('utf-8'));changed.append(p.stem)
planpath=H/'data/batch-plan.json';plan=json.loads(planpath.read_bytes())
for n in plan['module_order']:
 plan['source_sha256'][n]=hashlib.sha256((H/'lean'/(n+'.lean')).read_bytes()).hexdigest()
planpath.write_text(json.dumps(plan,indent=2)+'\n')
for i in range(254):
 p=H/'data'/('cover-'+str(i)+'.json');r=json.loads(p.read_bytes());r['source_sha256']=plan['source_sha256']['PartitionCover205_'+str(i)];p.write_text(json.dumps(r,indent=2)+'\n')
progress=H/'data/batch-progress.json'
(H/'logs/finite-batch-first-stop.json').write_bytes(progress.read_bytes())
trees=json.loads((H/'data/active-trees.json').read_bytes())
names=['HistoryParity205','DiagonalExtension205']+trees['module_order']
(H/'data/history-plan.json').write_text(json.dumps(dict(module_order=names),indent=2)+'\n')
print('Repaired unaccepted branch files:',len(changed),'History modules:',len(names))
