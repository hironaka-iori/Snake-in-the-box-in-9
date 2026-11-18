from pathlib import Path
import json,hashlib,shutil
H=Path(__file__).resolve().parents[1];P=H.parent/'238-three-count-recovery'
for d in ['lean','build','logs','data','scripts']:(H/d).mkdir(exist_ok=True)
for n in ['check_core.py','prepare_proof.py','native_resources.py','run_split_plan.py','publication.py']:
 s=(P/'scripts'/n).read_text(encoding='utf-8')
 if n=='publication.py':s=s.replace('Round238','Round239')
 (H/'scripts'/n).write_text(s,encoding='utf-8',newline='\n')
(H/'.gitattributes').write_text('* -text\n',encoding='utf-8')
data=json.loads((H/'data/four-count-audit.json').read_bytes());assert data['status']=='PASS_NO_NONZERO_INTEGER_SOLUTIONS'
le='\u2264';And='\u2227';mem='\u2208';div='\u2223';forall='\u2200';arrow='\u2192'
names=[]
for row in data['metric_classes']:
 n=row['index'];M=row['matrix'];A=row['adjugate'];D=row['determinant'];name=f'FourMatrix239_{n:03d}';names.append(name)
 lhs=[' + '.join(f'({M[i][j]})*x{j}' for j in range(4)) for i in range(4)]
 rhs=[' + '.join(f'({A[i][j]})*(315*s{j})' for j in range(4)) for i in range(4)]
 source='import Std\nset_option Elab.async false\nset_option maxRecDepth 30000\nset_option maxHeartbeats 4000000\nnamespace FourRecovery239\n'
 source+=f'private theorem ternary_mem (s : Int) (h : -1 {le} s {And} s {le} 1) : s {mem} ([-1,0,1] : List Int) := by\n  simp\n  omega\n'
 for i in range(4):
  full=' + '.join(f'({A[i][j]})*({lhs[j]})' for j in range(4))
  source+=f'private theorem row_{i} (x0 x1 x2 x3 : Int) : {D}*x{i} = {full} := by omega\n'
 source+=f'private theorem admissible :\n'+''.join(f'    {forall} s{i} {mem} ([-1,0,1] : List Int),\n' for i in range(4))
 source+=''.join(f'    ({D} {div} ({rhs[i]})) {arrow}\n' for i in range(4))
 source+='    '+f' {And} '.join(f's{i} = 0' for i in range(4))+' := by decide\n'
 source+=f'theorem zero_solution_{n:03d} (x0 x1 x2 x3 s0 s1 s2 s3 : Int)\n'
 source+=''.join(f'    (hs{i} : -1 {le} s{i} {And} s{i} {le} 1)\n' for i in range(4))
 source+=''.join(f'    (h{i} : {lhs[i]} = 315*s{i})\n' for i in range(4))
 source+='    : '+f' {And} '.join(f'x{i} = 0' for i in range(4))+' := by\n'
 for i in range(4):source+=f'  have e{i} := row_{i} x0 x1 x2 x3\n  rw [h0,h1,h2,h3] at e{i}\n'
 source+='  have z := admissible '+ ' '.join(f's{i} (ternary_mem s{i} hs{i})' for i in range(4))+'\n    '+' '.join(f'\u27e8x{i}, e{i}.symm\u27e9' for i in range(4))+'\n'
 source+='  rcases z with \u27e8rfl,rfl,rfl,rfl\u27e9\n  clear h0 h1 h2 h3\n  omega\n'
 source+=f'#print axioms zero_solution_{n:03d}\nend FourRecovery239\n'
 (H/'lean'/(name+'.lean')).write_text(source,encoding='utf-8',newline='\n')
plan=dict(modules_in_order=names,source_hashes={n:hashlib.sha256((H/'lean'/(n+'.lean')).read_bytes()).hexdigest() for n in names})
(H/'logs/four-matrix-plan.json').write_text(json.dumps(plan,indent=2)+'\n',encoding='utf-8',newline='\n');print('PREPARED',len(names),'exact matrix theorems')
