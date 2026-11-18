from pathlib import Path
import hashlib,json,itertools,shutil
H=Path(__file__).resolve().parents[1];cs=[0,35,-10,8,-16];le='\u2264';And='\u2227'
(H/'logs/initial-coefficient-sources').mkdir(exist_ok=True)
for i in range(5):shutil.copy2(H/'lean'/f'ThreeCoeff238_{i}.lean',H/'logs/initial-coefficient-sources'/f'ThreeCoeff238_{i}.lean')
shutil.copy2(H/'logs/three-coeff-split-plan.json',H/'logs/initial-coefficient-plan.json')
names=[]
for i,a in enumerate(cs):
 group=[]
 for j,b in enumerate(cs):
  for k,c in enumerate(cs):
   name=f'ThreeCoeffCase238_{i}{j}{k}';group.append(name);names.append(name)
   body=f'''import Std
set_option Elab.async false
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000
namespace CubeInverse
theorem coeff_{i}{j}{k} (x y z s t u : Int)
    (hx : -9 {le} x {And} x {le} 9) (hy : -9 {le} y {And} y {le} 9)
    (hz : -9 {le} z {And} z {le} 9)
    (hs : -1 {le} s {And} s {le} 1) (ht : -1 {le} t {And} t {le} 1)
    (hu : -1 {le} u {And} u {le} 1)
    (h1 : 128*x + ({a})*y + ({b})*z = 315*s)
    (h2 : ({a})*x + 128*y + ({c})*z = 315*t)
    (h3 : ({b})*x + ({c})*y + 128*z = 315*u) :
    x = 0 {And} y = 0 {And} z = 0 := by
  have sc : s = -1 \u2228 s = 0 \u2228 s = 1 := by omega
  have tc : t = -1 \u2228 t = 0 \u2228 t = 1 := by omega
  have uc : u = -1 \u2228 u = 0 \u2228 u = 1 := by omega
  rcases sc with rfl | rfl | rfl <;>
    rcases tc with rfl | rfl | rfl <;>
    rcases uc with rfl | rfl | rfl <;> omega
#print axioms coeff_{i}{j}{k}
end CubeInverse
'''
   (H/'lean'/(name+'.lean')).write_text(body,encoding='utf-8')
 source=(H/'lean'/f'ThreeCoeff238_{i}.lean').read_text(encoding='utf-8').replace('import Std','\n'.join('import '+n for n in group))
 source=source[:source.index(' := by')]+''' := by
  simp at hb hc
  rcases hb with rfl | rfl | rfl | rfl | rfl <;>
    rcases hc with rfl | rfl | rfl | rfl | rfl
'''+ '\n'.join(f'  \u00b7 exact coeff_{i}{j}{k} x y z s t u hx hy hz hs ht hu h1 h2 h3' for j in range(5) for k in range(5))+f'\n#print axioms three_coeff_{i}\nend CubeInverse\n'
 (H/'lean'/f'ThreeCoeff238_{i}.lean').write_text(source,encoding='utf-8');names.append(f'ThreeCoeff238_{i}')
names+=['ThreeCoefficients238','ThreeRecovery238']
plan=dict(modules_in_order=names,source_hashes={n:hashlib.sha256((H/'lean'/(n+'.lean')).read_bytes()).hexdigest() for n in names})
(H/'logs/three-coeff-split-plan.json').write_text(json.dumps(plan,indent=2)+'\n',encoding='utf-8');print('SPLIT',len(names))
