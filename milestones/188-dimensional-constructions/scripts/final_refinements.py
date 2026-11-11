from pathlib import Path
import json,hashlib
H=Path('E:/Snake-in-a-box/milestones/188-dimensional-constructions')
# Preserve the original restricted model and results; the new model allows
# an outer path consisting of one vertex.
p=H/'scripts/two_cross_search.py';backup=H/'scripts/two_cross_search_nontrivial.py'
if not backup.exists():backup.write_bytes(p.read_bytes())
s=backup.read_text()
s=s.replace('model.add(deg>=x[v]);model.add(deg<=2*x[v])','model.add(deg<=2*x[v])\n        if v not in ports:model.add(deg>=x[v])').replace('model.add(deg==1)','model.add(deg<=1)')
s=s.replace("'tag':tag,","'tag':tag,'singleton_outer_paths_allowed':True,")
s=s.replace("'lift6to7-fixed24'","'lift6to7-fixed24-allow-singletons'").replace("'lift7to8-fixed50'","'lift7to8-fixed50-allow-singletons'").replace("'lift8to9-fixed95'","'lift8to9-fixed95-allow-singletons'")
p.write_text(s,encoding='utf-8',newline='\n')
order=json.loads((H/'data/current-order.json').read_text());old=[n for n in order if n.startswith('CubeRows8_')];new=[]
for i in range(99):
    name=f'CubeRow8_{i:03}188';new.append(name)
    s=f'''import CubeData8188
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Dimensional188.Witness8
theorem row{i} : Row ⟨{i},by omega⟩ := by
  unfold Row
  decide +kernel
#print axioms row{i}
end Dimensional188.Witness8
'''
    (H/'lean'/(name+'.lean')).write_text(s,encoding='utf-8',newline='\n')
idx=order.index(old[0]);order=[n for n in order if n not in old];order[idx:idx]=new
s='\n'.join('import '+n for n in new)+'\nnamespace Dimensional188.Witness8\ntheorem allRows (i : Fin 99) : Row i := by\n'
for i in range(98):
    s+=f'  by_cases h{i} : i.val = {i}\n  · have he : i = ⟨{i},by omega⟩ := by apply Fin.ext; exact h{i}\n    simpa only [he] using row{i}\n'
s+='  have he : i = ⟨98,by omega⟩ := by apply Fin.ext; simp only [Fin.val_mk]; omega\n  simpa only [he] using row98\n'
p=H/'lean/Witness8188.lean';original=p.read_text();tail=original[original.index('theorem path_distinct'):]
s+=tail;p.write_text(s,encoding='utf-8',newline='\n')
base=json.loads((H/'data/Witness8188-execution.json').read_text());base['new_module_order']=order;base['source_sha256']={n:hashlib.sha256((H/'lean'/(n+'.lean')).read_bytes()).hexdigest() for n in order}
for n in order:
    if not (H/'data'/(n+'-audit.json')).exists():
        (H/'data'/(n+'-execution.json')).write_text(json.dumps(base,indent=2)+'\n')
(H/'data/current-order.json').write_text(json.dumps(order,indent=2)+'\n')
(H/'scripts/final_refinements.py').write_bytes(Path(__file__).read_bytes())
