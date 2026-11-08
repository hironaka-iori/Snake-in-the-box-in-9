from pathlib import Path
import json,hashlib
H=Path('E:/Snake-in-a-box/milestones/185-critical-kernel')
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
read=lambda p:json.loads(p.read_text(encoding='utf-8-sig'))
p=H/'lean/Share185/Structure.lean';s=p.read_text();prefix=s[:s.index('theorem counts_ok')]
for part,thm in [('Counts','counts_ok'),('Totals','totals_ok')]:
 line=next(x for x in s.splitlines() if x.startswith('theorem '+thm))
 (H/'lean/Share185'/(part+'.lean')).write_text(prefix+line+'\n#print axioms '+thm+'\nend Snake9.LocalWindow.ShareWindow185\n',newline='\n')
p.write_text('import Share185.Counts\nimport Share185.Totals\n',newline='\n')
order=read(H/'data/current-order.json');i=order.index('Share185.Structure')
order=order[:i]+['Share185.Counts','Share185.Totals']+order[i:]
base=read(H/'data/Share185.Structure-execution.json');base['new_module_order']=order
base['source_sha256']={n:sha(H/'lean'/(n.replace('.','/')+'.lean')) for n in order}
for name in order:
 if (H/'data'/(name+'-audit.json')).exists():continue
 (H/'data'/(name+'-execution.json')).write_text(json.dumps(base,indent=2)+'\n')
(H/'data/current-order.json').write_text(json.dumps(order,indent=2)+'\n')
(H/'scripts/split_structure.py').write_bytes(Path(__file__).read_bytes())

