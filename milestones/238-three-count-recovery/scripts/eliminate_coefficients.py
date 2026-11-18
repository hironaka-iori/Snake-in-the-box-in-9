from pathlib import Path
import hashlib,json,shutil
H=Path(__file__).resolve().parents[1];cs=[0,35,-10,8,-16]
(H/'logs/before-elimination').mkdir(exist_ok=True)
changed=0
for i,a in enumerate(cs):
 for j,b in enumerate(cs):
  for k,c in enumerate(cs):
   name=f'ThreeCoeffCase238_{i}{j}{k}'
   if (H/'data'/(name+'-audit.json')).exists():continue
   p=H/'lean'/(name+'.lean');s=p.read_text(encoding='utf-8');shutil.copy2(p,H/'logs/before-elimination'/p.name)
   D=128**3+2*a*b*c-128*(a*a+b*b+c*c)
   adj=[[16384-c*c,b*c-128*a,a*c-128*b],[b*c-128*a,16384-b*b,a*b-128*c],[a*c-128*b,a*b-128*c,16384-a*a]]
   body=''
   for v,row in zip('xyz',adj):
    A,B,C=row
    body+=f'''  have e{v} : {D}*{v} = ({A})*(128*x+({a})*y+({b})*z) + ({B})*(({a})*x+128*y+({c})*z) + ({C})*(({b})*x+({c})*y+128*z) := by omega
  rw [h1,h2,h3] at e{v}
'''
   s=s.replace(' := by\n  have sc',' := by\n'+body+'  have sc')
   s=s.replace('rcases uc with rfl | rfl | rfl <;> omega','rcases uc with rfl | rfl | rfl <;>\n      clear h1 h2 h3 <;> omega')
   p.write_text(s,encoding='utf-8');changed+=1
planpath=H/'logs/three-coeff-split-plan.json';plan=json.loads(planpath.read_bytes())
plan['source_hashes']={n:hashlib.sha256((H/'lean'/(n+'.lean')).read_bytes()).hexdigest() for n in plan['modules_in_order']}
planpath.write_text(json.dumps(plan,indent=2)+'\n',encoding='utf-8');print('ELIMINATED',changed)
