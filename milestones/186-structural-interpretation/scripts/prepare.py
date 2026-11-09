"""Split exact structural obligations without changing the saved CNF."""
from pathlib import Path
import json,gzip,hashlib,sys,datetime
R=Path('E:/Snake-in-a-box');H=R/'milestones/186-structural-interpretation';P=R/'milestones/185-critical-kernel'
read=lambda p:json.loads(p.read_text(encoding='utf-8-sig'))
cache={}
def sha(p):
 p=str(p)
 if p not in cache:cache[p]=hashlib.sha256(Path(p).read_bytes()).hexdigest()
 return cache[p]
for d in ['scripts','data','lean/Share186','logs','build','source-before']:(H/d).mkdir(parents=True,exist_ok=True)
(H/'scripts/prepare.py').write_bytes(Path(__file__).read_bytes())
for n in ['check_core.py','native_resources.py']:(H/'scripts'/n).write_bytes((P/'scripts'/n).read_bytes())
pins={}
prior=read(P/'data/completion.json')
for name in prior['accepted_module_names']:
 rp=P/'data'/(name+'-audit.json');j=read(rp)
 assert j['status']=='PASS' and j['exit_code']==0 and j['stop_reason'] is None
 for k,d in [('source','source_sha256'),('object','olean_sha256'),('log','log_sha256')]:
  assert sha(j[k])==j[d];pins[j[k]]=j[d]
 pins[str(rp)]=sha(rp)
 for q,d in j['dependencies'].items():assert sha(q)==d,q;pins[q]=d
sem=json.loads(gzip.decompress((R/'milestones/180-share14-certificates/certificates/012034.meanings.json.gz').read_bytes()))
meta=read(P/'data/share185.json');rename={int(k):v for k,v in meta['original_to_new'].items()}
ctrs=sem['ctrs'];assert len(ctrs)==1 and ctrs[0][1:]==[2,['ends']]
lits=[2*rename[v] for v in ctrs[0][0]]
verts=[sem['meaning'][str(v)][1] for v in ctrs[0][0]]
assert all(sem['meaning'][str(v)][0]=='e' for v in ctrs[0][0])
assert len(lits)==286 and verts==sorted(set(verts))
chunks=[lits[i:i+16] for i in range(0,len(lits),16)]
vchunks=[verts[i:i+16] for i in range(0,len(verts),16)]
ns='Snake9.LocalWindow.ShareWindow185'
header='set_option maxRecDepth 100000\nset_option maxHeartbeats 0\nnamespace '+ns+'\nopen Snake9.LocalWindow.Tags Snake9.LocalWindow.Tags185\n'
end='end '+ns+'\n'
def write(name,s):
 p=H/'lean'/(name.replace('.','/')+'.lean');p.parent.mkdir(parents=True,exist_ok=True);assert not p.exists();p.write_text(s,newline='\n')
s='import Share185.DirectData\n'+header
for i,(a,b) in enumerate(zip(chunks,vchunks)):
 s+=f'def epLits{i} : List Nat := {a}\ndef epVerts{i} : List Nat := {b}\n'
s+='def epLits : List Nat := '+' ++ '.join('epLits'+str(i) for i in range(len(chunks)))+'\n'
s+='def epVerts : List Nat := '+' ++ '.join('epVerts'+str(i) for i in range(len(chunks)))+'\n'
s+='theorem endpoint_counter_data : ctrs = [⟨epLits,2,.ends⟩] := by rfl\n'
s+='#print axioms endpoint_counter_data\n'+end
write('Share186.EndpointData',s)
order=['Share186.EndpointData']
for i in range(len(chunks)):
 name=f'Share186.Endpoint{i:02d}';order.append(name)
 s='import Share186.EndpointData\n'+header
 s+=f'theorem ep_pos{i} : epLits{i}.all (posE meaningDirect) = true := by decide +kernel\n'
 s+=f'theorem ep_map{i} : epLits{i}.map (vl meaningDirect) = epVerts{i} := by decide +kernel\n'
 s+=f'#print axioms ep_pos{i}\n#print axioms ep_map{i}\n'+end
 write(name,s)
s='import Share186.EndpointData\n'+header
s+='theorem ep_sorted : pw epVerts = true := by decide +kernel\n#print axioms ep_sorted\n'+end
write('Share186.EndpointSorted',s);order+=['Share186.EndpointSorted']
s=''.join('import '+n+'\n' for n in order[1:])+header
s+='theorem ep_positive : epLits.all (posE meaningDirect) = true := by\n  simp only [epLits,List.all_append,'+','.join('ep_pos'+str(i) for i in range(len(chunks)))+',Bool.and_self]\n'
s+='theorem ep_mapping : epLits.map (vl meaningDirect) = epVerts := by\n  simp only [epLits,epVerts,List.map_append,'+','.join('ep_map'+str(i) for i in range(len(chunks)))+']\n'
s+='theorem counts_ok : ctrs.all (ctrOK meaningDirect (centresK window bounds)) = true := by\n'
s+='  have hb : epLits.all (baseOK meaningDirect) = true := by\n    apply List.all_eq_true.mpr\n    intro a ha\n    have hp := List.all_eq_true.mp ep_positive a ha\n    simp only [posE,Bool.and_eq_true] at hp\n    simp [baseOK,hp.1.2,hp.2]\n'
s+='  rw [endpoint_counter_data]\n  simp only [List.all_cons,List.all_nil,Bool.and_true,ctrOK]\n  simp only [hb,ep_positive,ep_mapping,ep_sorted,beq_self_eq_true,Bool.and_self]\n'
s+='#print axioms counts_ok\n'+end
write('Share186.Counts',s);order+=['Share186.Counts']
for i in range(70):
 name=f'Share186.Total{i:02d}';order.append(name)
 s='import Share185.DirectData\n'+header
 s+=f'theorem total{i}_ok : totOK meaningDirect smeaningDirect window (centresK window bounds) (tots.getD {i} dfltTot) = true := by decide +kernel\n'
 s+=f'#print axioms total{i}_ok\n'+end
 write(name,s)
base=read(P/'data/Share185.DirectData-execution.json')
plan=dict(new_module_order=order,source_sha256={n:sha(H/'lean'/(n.replace('.','/')+'.lean')) for n in order},
 input_pins=pins,lean_bin=base['lean_bin'],search_paths=[str(H/'build'),str(P/'build'),str(R/'milestones/147-countfree-clause-semantics/build')],checker_sha256=sha(H/'scripts/check_core.py'))
pins[str(H/'scripts/native_resources.py')]=sha(H/'scripts/native_resources.py')
for n in order:(H/'data'/(n+'-execution.json')).write_text(json.dumps(plan,indent=2)+'\n')
(H/'data/current-order.json').write_text(json.dumps(order,indent=2)+'\n')
(H/'data/preparation.json').write_text(json.dumps(dict(round=186,previous_turn='PROGRESS',started_utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),
 endpoint_literals=286,endpoint_batches=len(chunks),individual_small_totalizers=70,
 inherited_accepted_modules=len(prior['accepted_module_names']),initial_modules=len(order),
 full_structure=False,full_clause_interpretation=False),indent=2)+'\n')
print('PREPARED',len(order),'modules;',len(chunks),'endpoint groups and 70 individual totals.')

