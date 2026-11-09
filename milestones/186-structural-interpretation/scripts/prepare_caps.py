"""Prepare small cap-literal checks and a structural permutation proof."""
from pathlib import Path
import json,gzip,hashlib,copy
R=Path('E:/Snake-in-a-box');H=R/'milestones/186-structural-interpretation';P=R/'milestones/185-critical-kernel'
read=lambda p:json.loads(p.read_text(encoding='utf-8-sig'))
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
sem=json.loads(gzip.decompress((R/'milestones/180-share14-certificates/certificates/012034.meanings.json.gz').read_bytes()))
delta=json.loads(gzip.decompress((R/'milestones/183-critical-floor15/certificates/012034-floor15.delta.json.gz').read_bytes()))
rename={int(k):v for k,v in read(P/'data/share185.json')['original_to_new'].items()}
oldbits=sem['tots'][70][0];newbits=delta['new_cap_bits'][len(oldbits):]
assert len(oldbits)==490 and len(newbits)==35
meaning={int(k):v for k,v in sem['smeaning'].items()}
meaning.update({int(k):v[:3] for k,v in delta['new_meanings'].items() if v[0]=='u'})
corners=[meaning[oldbits[14*i]][1] for i in range(35)]
spec14=[[tuple(x) for x in row] for row in sem['tots'][70][1][1]]
spec15=[[(k,15) for k,t in row] for row in spec14]
ns='Snake9.LocalWindow.ShareWindow185'
head='set_option maxRecDepth 100000\nset_option maxHeartbeats 0\nnamespace '+ns+'\nopen Snake9.LocalWindow.Tags Snake9.LocalWindow.Tags185\n'
end='end '+ns+'\n'
def write(n,s):
 p=H/'lean'/(n.replace('.','/')+'.lean');p.parent.mkdir(parents=True,exist_ok=True);assert not p.exists();p.write_text(s,newline='\n')
s='import Share185.DirectData\n'+head
parts={}
for label,bits in [('base',oldbits),('extra',newbits)]:
 parts[label]=[bits[i:i+16] for i in range(0,len(bits),16)]
 for i,bs in enumerate(parts[label]):
  assert all(meaning[v][0]=='u' for v in bs)
  s+=f'def {label}Lits{i} : List Nat := '+str([2*rename[v] for v in bs])+'\n'
  s+=f'def {label}Pairs{i} : List (Nat × Nat) := '+str([tuple(meaning[v][1:]) for v in bs])+'\n'
 for what in ['Lits','Pairs']:
  typ='Nat' if what=='Lits' else '(Nat × Nat)'
  s+=f'def cap{label.title()}{what} : List {typ} := '+' ++ '.join(label+what+str(i) for i in range(len(parts[label])))+'\n'
s+=f'def capCorners : List Nat := {corners}\ndef capSpec14 : List (List (Nat × Nat)) := {spec14}\ndef capSpec15 : List (List (Nat × Nat)) := {spec15}\n'
s+='theorem cap70_data : tots.getD 70 dfltTot = ⟨capBaseLits,.cap capSpec14⟩ := by rfl\n'
s+='theorem cap71_data : tots.getD 71 dfltTot = ⟨capBaseLits ++ capExtraLits,.cap capSpec15⟩ := by rfl\n'
s+='#print axioms cap70_data\n#print axioms cap71_data\n'+end
write('Share186.CapData',s);order=['Share186.CapData']
for label in parts:
 for i in range(len(parts[label])):
  name=f'Share186.Cap{label.title()}{i:02d}';order.append(name)
  s='import Share186.CapData\n'+head
  s+=f'theorem {label}_pos{i} : {label}Lits{i}.all (posU meaningDirect smeaningDirect) = true := by decide +kernel\n'
  s+=f'theorem {label}_map{i} : {label}Lits{i}.map (uQT smeaningDirect) = {label}Pairs{i} := by decide +kernel\n'
  s+=f'#print axioms {label}_pos{i}\n#print axioms {label}_map{i}\n'+end
  write(name,s)
s='import Share186.CapData\n'+head
s+=r"""
theorem split_layers_perm {α β : Type} (xs : List α) (f g : α → List β) :
    (xs.flatMap (fun x => f x ++ g x)).Perm (xs.flatMap f ++ xs.flatMap g) := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    simp only [List.flatMap_cons]
    apply (ih.append_left (f x ++ g x)).trans
    simpa only [List.append_assoc] using
      (List.perm_append_comm_assoc (g x) (xs.flatMap f) (xs.flatMap g)).append_left (f x)

theorem threshold_layers_perm (qs : List Nat) :
    ((qs.flatMap (fun q => (List.range 14).map (fun t => (q,t+1)))) ++
      qs.map (fun q => (q,15))).Perm
    (qs.flatMap (fun q => (List.range 15).map (fun t => (q,t+1)))) := by
  have h := (split_layers_perm qs
    (fun q => (List.range 14).map (fun t => (q,t+1)))
    (fun q => [(q,15)])).symm
  have hr (q : Nat) : (List.range 15).map (fun t => (q,t+1)) =
      (List.range 14).map (fun t => (q,t+1)) ++ [(q,15)] := by
    rw [show 15 = 14+1 from rfl,List.range_succ,List.map_append]
    rfl
  simpa only [← List.map_eq_flatMap, ← hr] using h

theorem pair_isPerm_of_perm {xs ys : List (Nat × Nat)} (h : xs.Perm ys) :
    xs.isPerm ys = true := by
  have heq : (instBEqProd : BEq (Nat × Nat)) = instBEqOfDecidableEq := by
    apply congrArg BEq.mk
    funext a b
    exact Bool.beq_eq_decide_eq a b
  rw [heq]
  exact List.isPerm_iff.mpr h

theorem base_of_posU (l : List Nat) (h : l.all (posU meaningDirect smeaningDirect) = true) :
    l.all (baseOKS meaningDirect smeaningDirect) = true := by
  apply List.all_eq_true.mpr
  intro a ha
  have hu := Bool.and_eq_true.mp (List.all_eq_true.mp h a ha)
  have hp := posS_parts hu.1
  simp [baseOKS,hp.2.1,hp.2.2,hu.2]

#print axioms split_layers_perm
#print axioms threshold_layers_perm
#print axioms pair_isPerm_of_perm
#print axioms base_of_posU
"""
write('Share186.CapLemmas',s+end);order+=['Share186.CapLemmas']
s=''.join('import '+n+'\n' for n in order)+head
for label in parts:
 N=len(parts[label]);title=label.title()
 s+=f'theorem cap{title}_pos : cap{title}Lits.all (posU meaningDirect smeaningDirect) = true := by\n  simp only [cap{title}Lits,List.all_append,'+','.join(label+'_pos'+str(i) for i in range(N))+',Bool.and_self]\n'
 s+=f'theorem cap{title}_map : cap{title}Lits.map (uQT smeaningDirect) = cap{title}Pairs := by\n  simp only [cap{title}Lits,cap{title}Pairs,List.map_append,'+','.join(label+'_map'+str(i) for i in range(N))+']\n'
s+='theorem capBase_rows : capBasePairs = capCorners.flatMap (fun q => (List.range 14).map (fun t => (q,t+1))) := by rfl\n'
s+='theorem capExtra_rows : capExtraPairs = capCorners.map (fun q => (q,15)) := by rfl\n'
s+='theorem cap14_rows : capL (centresK window bounds) capSpec14 = capBasePairs := by decide +kernel\n'
s+='theorem cap15_rows : capL (centresK window bounds) capSpec15 = capCorners.flatMap (fun q => (List.range 15).map (fun t => (q,t+1))) := by decide +kernel\n'
s+='theorem spec14_ok : capSpec14.all (fun s => subl (s.map (·.1)) (List.range 9)) = true := by decide +kernel\n'
s+='theorem spec15_ok : capSpec15.all (fun s => subl (s.map (·.1)) (List.range 9)) = true := by decide +kernel\n'
s+='theorem total70_ok : totOK meaningDirect smeaningDirect window (centresK window bounds) (tots.getD 70 dfltTot) = true := by\n'
s+='  rw [cap70_data]\n  simp only [totOK,base_of_posU _ capBase_pos,capBase_pos,capBase_map,cap14_rows,spec14_ok]\n'
s+='  have hp := pair_isPerm_of_perm (List.Perm.refl capBasePairs)\n  simp only [hp,Bool.and_self]\n'
s+='theorem total71_ok : totOK meaningDirect smeaningDirect window (centresK window bounds) (tots.getD 71 dfltTot) = true := by\n'
s+='  have hu : (capBaseLits ++ capExtraLits).all (posU meaningDirect smeaningDirect) = true := by simp only [List.all_append,capBase_pos,capExtra_pos,Bool.and_self]\n'
s+='  have hp : (capBasePairs ++ capExtraPairs).isPerm (capL (centresK window bounds) capSpec15) = true := by\n'
s+='    apply pair_isPerm_of_perm\n    rw [capBase_rows,capExtra_rows,cap15_rows]\n    exact threshold_layers_perm capCorners\n'
s+='  rw [cap71_data]\n  simp only [totOK,base_of_posU _ hu,hu,List.map_append,capBase_map,capExtra_map,hp,spec15_ok,Bool.and_self]\n'
s+='#print axioms total70_ok\n#print axioms total71_ok\n'+end
write('Share186.CapTotals',s);order+=['Share186.CapTotals']
old=read(H/'data/current-order.json');base=read(H/'data/Share186.EndpointData-execution.json')
base['new_module_order']=old+order;base['source_sha256'].update({n:sha(H/'lean'/(n.replace('.','/')+'.lean')) for n in order})
for n in order:(H/'data'/(n+'-execution.json')).write_text(json.dumps(base,indent=2)+'\n')
(H/'data/cap-order.json').write_text(json.dumps(order,indent=2)+'\n')
(H/'scripts/prepare_caps.py').write_bytes(Path(__file__).read_bytes())
print('CAP_MODULES',len(order),'with per-block interpretation and a structural permutation proof.')

