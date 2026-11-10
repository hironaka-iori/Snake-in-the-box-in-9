"""Continue the exact critical input using smaller clause proofs."""
from pathlib import Path
import json,hashlib,datetime,re
R=Path('E:/Snake-in-a-box');P=R/'milestones/186-structural-interpretation';H=R/'milestones/187-clause-interpretation'
assert not H.exists()
read=lambda p:json.loads(p.read_text(encoding='utf-8-sig'))
cache={}
def sha(p):
 p=str(p)
 if p not in cache:cache[p]=hashlib.sha256(Path(p).read_bytes()).hexdigest()
 return cache[p]
for d in ['scripts','data','lean/Share187','build','logs','source-before']:(H/d).mkdir(parents=True,exist_ok=True)
pins={};prior=read(P/'data/completion.json')
for n in prior['accepted_module_names']:
 rp=P/'data'/(n+'-audit.json');j=read(rp)
 assert j['status']=='PASS' and j['exit_code']==0 and j['stop_reason'] is None
 for a,b in [('source','source_sha256'),('object','olean_sha256'),('log','log_sha256')]:assert sha(j[a])==j[b];pins[j[a]]=j[b]
 for p,d in j['dependencies'].items():assert sha(p)==d,p;pins[p]=d
 pins[str(rp)]=sha(rp)
for n in ['check_core.py','native_resources.py']:(H/'scripts'/n).write_bytes((P/'scripts'/n).read_bytes())
pins[str(H/'scripts/native_resources.py')]=sha(H/'scripts/native_resources.py')
head='set_option maxRecDepth 100000\nset_option maxHeartbeats 0\nnamespace Snake9.LocalWindow.ShareWindow185\nopen Snake9.LocalWindow.Tags Snake9.LocalWindow.Tags185\n';end='end Snake9.LocalWindow.ShareWindow185\n'
params='meaningDirect smeaningDirect resolution ctrs tots window cap'
def put(n,s):
 p=H/'lean'/(n.replace('.','/')+'.lean');assert not p.exists();p.write_text(s,encoding='utf-8',newline='\n')
put('Share187.Split','import Share186.ClauseAppend\n'+head+'''theorem ckAllS_of_split (M : MT) (X : MS) (r : Nat) (cs : List Ctr)
    (ts : List Tot) (w : List Nat) (cap k : Nat)
    (a : List TagS) (b : List (List Nat))
    (hlen : (a.take k).length = (b.take k).length)
    (hl : ckAllS M X r cs ts w cap (a.take k) (b.take k) = true)
    (hr : ckAllS M X r cs ts w cap (a.drop k) (b.drop k) = true) :
    ckAllS M X r cs ts w cap a b = true := by
  have h := ckAllS_append_true M X r cs ts w cap
    (a.take k) (a.drop k) (b.take k) (b.drop k) hlen hl hr
  simpa only [List.take_append_drop] using h
#print axioms ckAllS_of_split
'''+end)
order=['Share187.Split']
for i in range(38,98):
 count=4 if i<97 else 1
 for part in range(count):
  n=f'Share187.Piece{i:02d}_{part}';order.append(n)
  terms=[]
  for label in ['tags','raw']:
   t=f'{label}{i}'
   if part:t=f'({t}.drop {part*32})'
   if part<count-1:t=f'({t}.take 32)'
   terms.append(t)
  s='import Share185.DirectData\n'+head+f'theorem piece{i}_{part} : ckAllS {params} {terms[0]} {terms[1]} = true := by decide +kernel\n#print axioms piece{i}_{part}\n'+end
  put(n,s)
 n=f'Share187.Shard{i:02d}';order.append(n)
 s='import Share187.Split\n'+''.join(f'import Share187.Piece{i:02d}_{part}\n' for part in range(count))+head
 s+=f'theorem shard{i} : ckAllS {params} tags{i} raw{i} = true := by\n'
 if count==1:s+=f'  exact piece{i}_0\n'
 else:
  for part in [2,1,0]:
   a=f'(tags{i}.drop {part*32})' if part else f'tags{i}'
   b=f'(raw{i}.drop {part*32})' if part else f'raw{i}'
   s+=f'  have h{part} : ckAllS {params} {a} {b} = true := by\n'
   s+=f'    apply ckAllS_of_split {params} 32 {a} {b}\n'
   s+='    · decide +kernel\n'
   s+=f'    · exact piece{i}_{part}\n'
   tail=f'piece{i}_3' if part==2 else f'h{part+1}'
   s+=f'    · simpa only [List.drop_drop,Nat.reduceAdd] using {tail}\n'
  s+='  exact h0\n'
 s+=f'#print axioms shard{i}\n'+end;put(n,s)
compose=(P/'lean/Share185/Compose.lean').read_text()
for i in range(38,98):compose=compose.replace(f'import Share185.Shard{i:02d}',f'import Share187.Shard{i:02d}')
put('Share187.Compose',compose);order+=['Share187.Compose']
base=read(P/'data/Share185.Shard38-execution.json')
plan=dict(new_module_order=order,source_sha256={n:sha(H/'lean'/(n.replace('.','/')+'.lean')) for n in order},input_pins=pins,lean_bin=base['lean_bin'],
 search_paths=[str(H/'build'),str(P/'build'),str(R/'milestones/185-critical-kernel/build'),str(R/'milestones/147-countfree-clause-semantics/build')],checker_sha256=sha(H/'scripts/check_core.py'))
for n in order:(H/'data'/(n+'-execution.json')).write_text(json.dumps(plan,indent=2)+'\n')
(H/'data/current-order.json').write_text(json.dumps(order,indent=2)+'\n')
(H/'scripts/run_semantics.py').write_text((P/'scripts/run_semantics.py').read_text().replace('186-structural-interpretation','187-clause-interpretation'),newline='\n')
(H/'scripts/prepare.py').write_bytes(Path(__file__).read_bytes())
(H/'data/preparation.json').write_text(json.dumps(dict(round=187,previous_goal_turn='PROGRESS',started_utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),inherited_modules=209,previous_inherited_modules=98,new_modules=len(order),piece_size=32,input_clauses=12424,previous_checked_clauses=4864,remaining_clauses=7560,validated_dependency_files=len(cache)),indent=2)+'\n')
print('PREPARED',len(order),'modules for all remaining clause batches and composition.',flush=True)
