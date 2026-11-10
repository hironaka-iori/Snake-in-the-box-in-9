from pathlib import Path
import json,hashlib
H=Path('E:/Snake-in-a-box/milestones/187-clause-interpretation');read=lambda p:json.loads(p.read_text())
head='set_option maxRecDepth 100000\nset_option maxHeartbeats 0\nnamespace Snake9.LocalWindow.ShareWindow185\nopen Snake9.LocalWindow.Tags Snake9.LocalWindow.Tags185\n';end='end Snake9.LocalWindow.ShareWindow185\n'
params='meaningDirect smeaningDirect resolution ctrs tots window cap'
order=read(H/'data/current-order.json');new=[]
for i in [38,39]:
 names=[]
 for k in range(16):
  n=f'Share187.Cut{i}_{k:02d}';names.append(n)
  a=f'(tags{i}.drop {k*8})' if k else f'tags{i}';b=f'(raw{i}.drop {k*8})' if k else f'raw{i}'
  if k<15:a=f'({a}.take 8)';b=f'({b}.take 8)'
  s='import Share185.DirectData\n'+head+f'theorem cut{i}_{k} : ckAllS {params} {a} {b} = true := by decide +kernel\n#print axioms cut{i}_{k}\n'+end
  (H/'lean'/(n.replace('.','/')+'.lean')).write_text(s,encoding='utf-8',newline='\n')
 s='import Share187.Split\n'+''.join('import '+n+'\n' for n in names)+head+f'theorem shard{i} : ckAllS {params} tags{i} raw{i} = true := by\n'
 for k in range(14,-1,-1):
  a=f'(tags{i}.drop {k*8})' if k else f'tags{i}';b=f'(raw{i}.drop {k*8})' if k else f'raw{i}'
  s+=f'  have h{k} : ckAllS {params} {a} {b} = true := by\n    apply ckAllS_of_split {params} 8 {a} {b}\n    · decide +kernel\n    · exact cut{i}_{k}\n'
  tail=f'cut{i}_15' if k==14 else f'h{k+1}'
  s+=f'    · simpa only [List.drop_drop,Nat.reduceAdd] using {tail}\n'
 s+='  exact h0\n'+f'#print axioms shard{i}\n'+end
 (H/f'lean/Share187/Shard{i}.lean').write_text(s,encoding='utf-8',newline='\n')
 order=[n for n in order if not n.startswith(f'Share187.Piece{i}_')]
 ix=order.index(f'Share187.Shard{i}');order[ix:ix]=names
base=read(H/'data/Share187.Compose-execution.json');base['new_module_order']=order
base['source_sha256']={n:hashlib.sha256((H/'lean'/(n.replace('.','/')+'.lean')).read_bytes()).hexdigest() for n in order}
for n in order:
 if not (H/'data'/(n+'-audit.json')).exists():(H/'data'/(n+'-execution.json')).write_text(json.dumps(base,indent=2)+'\n')
(H/'data/current-order.json').write_text(json.dumps(order,indent=2)+'\n')
(H/'scripts/refine_cut_pieces.py').write_bytes(Path(__file__).read_bytes());print('planned',len(order),'modules; cycle cuts in groups of eight')
