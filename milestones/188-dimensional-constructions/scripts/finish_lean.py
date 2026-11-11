from pathlib import Path
import json, hashlib
H=Path('E:/Snake-in-a-box/milestones/188-dimensional-constructions')
p=H/'lean/Reconstruction7188.lean'
s=p.read_text().replace('Compatible p q := by decide +kernel','Compatible p q := by\n  unfold Compatible\n  decide +kernel').replace('Compatible q r := by decide +kernel','Compatible q r := by\n  unfold Compatible\n  decide +kernel')
p.write_text(s,encoding='utf-8',newline='\n')
order=json.loads((H/'data/current-order.json').read_text())
names=[]
for k,start in enumerate(range(0,98,7)):
    size=min(7,98-start); name=f'CubeSteps8_{k:02}188';names.append(name)
    text=f'''import CubeData8188
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Dimensional188.Witness8
theorem steps{k} : ∀ j : Fin {size},
  (pathVertex ⟨{start}+j.val+1,by omega⟩).val =
  Nat.xor (pathVertex ⟨{start}+j.val,by omega⟩).val (2^transitions[{start}+j.val]!) := by decide +kernel
#print axioms steps{k}
end Dimensional188.Witness8
'''
    (H/'lean'/(name+'.lean')).write_text(text,encoding='utf-8',newline='\n')
s='\n'.join('import '+n for n in names)+'\nnamespace Dimensional188.Witness8\ntheorem transitions_agree (i : Fin 98) :\n  (pathVertex ⟨i.val+1,by omega⟩).val = Nat.xor (pathVertex ⟨i.val,by omega⟩).val (2^transitions[i.val]!) := by\n'
for k,start in enumerate(range(0,98,7)):
    prefix=f'  by_cases h{k} : i.val < {start+7}\n  · ' if k<13 else '  '
    s+=prefix+f'have h := steps{k} ⟨i.val-{start},by omega⟩\n'+('    ' if k<13 else '  ')+f'have he : {start}+(i.val-{start})=i.val := by omega\n'+('    ' if k<13 else '  ')+f'simpa only [he] using h\n'
s+='#print axioms transitions_agree\nend Dimensional188.Witness8\n'
(H/'lean/CubeTransitions8188.lean').write_text(s,encoding='utf-8',newline='\n')
i=order.index('CubeTransitions8188');order[i:i]=names
base=json.loads((H/'data/CubeTransitions8188-execution.json').read_text())
base['new_module_order']=order;base['source_sha256']={n:hashlib.sha256((H/'lean'/(n+'.lean')).read_bytes()).hexdigest() for n in order}
for n in order:
    if not (H/'data'/(n+'-audit.json')).exists():
        (H/'data'/(n+'-execution.json')).write_text(json.dumps(base,indent=2)+'\n')
(H/'data/current-order.json').write_text(json.dumps(order,indent=2)+'\n')
(H/'scripts/finish_lean.py').write_bytes(Path(__file__).read_bytes())
