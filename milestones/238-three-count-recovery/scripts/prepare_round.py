from pathlib import Path
import shutil,json,hashlib
H=Path(__file__).resolve().parents[1];P=H.parent/'237-parity-reconstruction'
for d in ['lean','build','data','logs','scripts']:(H/d).mkdir(exist_ok=True)
for n in ['check_core.py','prepare_proof.py','native_resources.py','run_split_plan.py','publication.py']:
 s=(P/'scripts'/n).read_text(encoding='utf-8')
 if n=='publication.py':s=s.replace('Round237','Round238')
 (H/'scripts'/n).write_text(s,encoding='utf-8')
for module in ['CubeInverse','CubeInverseRecovery237','CubeInverseReconstruct237','CubeInverseBase237']+[f'CubeInverseKernel237_{i:02d}' for i in range(16)]:
 for d,ext in [('lean','.lean'),('build','.olean'),('data','-audit.json')]:shutil.copy2(P/d/(module+ext),H/d/(module+ext))
(H/'.gitattributes').write_text('* -text\n',encoding='utf-8')
cs=[0,35,-10,8,-16];names=[]
le='\u2264';mem='\u2208';and_='\u2227'
for i,a in enumerate(cs):
 name=f'ThreeCoeff238_{i}';names.append(name)
 source=f'''import Std
set_option Elab.async false
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000
namespace CubeInverse
theorem three_coeff_{i} (b c x y z s t u : Int)
    (hb : b {mem} ([0,35,-10,8,-16] : List Int))
    (hc : c {mem} ([0,35,-10,8,-16] : List Int))
    (hx : -9 {le} x {and_} x {le} 9) (hy : -9 {le} y {and_} y {le} 9)
    (hz : -9 {le} z {and_} z {le} 9)
    (hs : -1 {le} s {and_} s {le} 1) (ht : -1 {le} t {and_} t {le} 1)
    (hu : -1 {le} u {and_} u {le} 1)
    (h1 : 128*x + ({a})*y + b*z = 315*s)
    (h2 : ({a})*x + 128*y + c*z = 315*t)
    (h3 : b*x + c*y + 128*z = 315*u) :
    x = 0 {and_} y = 0 {and_} z = 0 := by
  simp at hb hc
  rcases hb with rfl | rfl | rfl | rfl | rfl <;>
    rcases hc with rfl | rfl | rfl | rfl | rfl <;> omega
#print axioms three_coeff_{i}
end CubeInverse
'''
 (H/'lean'/(name+'.lean')).write_text(source,encoding='utf-8')
source='\n'.join('import '+n for n in names)+f'''
set_option Elab.async false
namespace CubeInverse
theorem three_coeff (a b c x y z s t u : Int)
    (ha : a {mem} ([0,35,-10,8,-16] : List Int))
    (hb : b {mem} ([0,35,-10,8,-16] : List Int))
    (hc : c {mem} ([0,35,-10,8,-16] : List Int))
    (hx : -9 {le} x {and_} x {le} 9) (hy : -9 {le} y {and_} y {le} 9)
    (hz : -9 {le} z {and_} z {le} 9)
    (hs : -1 {le} s {and_} s {le} 1) (ht : -1 {le} t {and_} t {le} 1)
    (hu : -1 {le} u {and_} u {le} 1)
    (h1 : 128*x + a*y + b*z = 315*s)
    (h2 : a*x + 128*y + c*z = 315*t)
    (h3 : b*x + c*y + 128*z = 315*u) :
    x = 0 {and_} y = 0 {and_} z = 0 := by
  simp at ha
  rcases ha with rfl | rfl | rfl | rfl | rfl
'''+ '\n'.join(f'  \u00b7 exact three_coeff_{i} b c x y z s t u hb hc hx hy hz hs ht hu h1 h2 h3' for i in range(5))+'\n#print axioms three_coeff\nend CubeInverse\n'
(H/'lean/ThreeCoefficients238.lean').write_text(source,encoding='utf-8');names.append('ThreeCoefficients238')
plan=dict(modules_in_order=names,source_hashes={n:hashlib.sha256((H/'lean'/(n+'.lean')).read_bytes()).hexdigest() for n in names})
(H/'logs/three-coeff-split-plan.json').write_text(json.dumps(plan,indent=2)+'\n',encoding='utf-8')
print('PREPARED',len(names))
