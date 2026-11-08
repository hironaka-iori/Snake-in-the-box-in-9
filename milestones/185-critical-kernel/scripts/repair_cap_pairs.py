from pathlib import Path
import json,hashlib,re
H=Path('E:/Snake-in-a-box/milestones/185-critical-kernel')
p=H/'lean/Share185/CoreData.lean';s=p.read_text()
s,n=re.subn(r'\(\.cap ([^\n]*?)\)',lambda m:'(.cap '+re.sub(r'\[(\d+), (\d+)\]',r'(\1, \2)',m[1])+')',s)
assert n==2,n
p.write_text(s,newline='\n')
order=json.loads((H/'data/current-order.json').read_text());d=hashlib.sha256(p.read_bytes()).hexdigest()
for name in order:
 if (H/'data'/(name+'-audit.json')).exists():continue
 q=H/'data'/(name+'-execution.json');j=json.loads(q.read_text(encoding='utf-8-sig'));j['source_sha256']['Share185.CoreData']=d
 q.write_text(json.dumps(j,indent=2)+'\n')
(H/'scripts/repair_cap_pairs.py').write_bytes(Path(__file__).read_bytes())
print('Restored tuple syntax in both cap specifications.')

