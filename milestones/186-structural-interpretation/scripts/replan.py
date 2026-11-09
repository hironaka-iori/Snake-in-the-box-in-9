from pathlib import Path
import json,hashlib
H=Path('E:/Snake-in-a-box/milestones/186-structural-interpretation')
read=lambda p:json.loads(p.read_text(encoding='utf-8-sig'))
def replan(order):
 base=read(H/'data/Share186.CapTotals-execution.json');base['new_module_order']=order
 base['source_sha256']={n:hashlib.sha256((H/'lean'/(n.replace('.','/')+'.lean')).read_bytes()).hexdigest() for n in order}
 for n in order:
  if not (H/'data'/(n+'-audit.json')).exists():(H/'data'/(n+'-execution.json')).write_text(json.dumps(base,indent=2)+'\n')
 (H/'data/current-order.json').write_text(json.dumps(order,indent=2)+'\n')
if __name__=='__main__':
 p=H/'lean/Share186/EndpointSorted.lean';s=p.read_text()
 s=s.replace('= true := by\n  simp','= true := by\n'+''.join(f'  have hx{i} := ep_cross{i}\n  simp only [List.append_assoc] at hx{i}\n' for i in range(17))+'  simp')
 for i in range(17):s=s.replace(f',ep_cross{i},',f',hx{i},')
 p.write_text(s,encoding='utf-8',newline='\n')
 order=read(H/'data/current-order.json')+read(H/'data/remaining-order.json')
 order.remove('Share186.CapData');order.remove('Share186.CapLemmas')
 ix=order.index('Share186.Total00');order[ix:ix]=['Share186.CapData','Share186.CapLemmas']
 replan(order)
 (H/'scripts/replan.py').write_bytes(Path(__file__).read_bytes())
 print('planned',len(order))
