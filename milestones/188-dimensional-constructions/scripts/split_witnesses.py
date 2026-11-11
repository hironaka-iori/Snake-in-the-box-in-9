from pathlib import Path
import json,hashlib
H=Path('E:/Snake-in-a-box/milestones/188-dimensional-constructions')
seeds=json.loads((H/'data/lower-dimensional-seeds.json').read_text())
order=['LayerJoining','TwoCrossings188','Witness6188']
for n,width in [(7,8),(8,4)]:
    s=seeds[str(n)];N=len(s['vertices']);size=1<<n;data=f'CubeData{n}188';ns=f'Dimensional188.Witness{n}';profile=s['profiles'][0]
    src=f'''import LayerJoining
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace {ns}
def Adj (u v : Fin {size}) : Prop := (List.range {n}).any (fun k => v.val == Nat.xor u.val (2^k)) = true
instance (u v : Fin {size}) : Decidable (Adj u v) := inferInstanceAs (Decidable (_ = true))
def pathValues : Array Nat := #[{', '.join(map(str,s['vertices']))}]
def pathVertex (i : Fin {N}) : Fin {size} := ⟨pathValues[i.val]! % {size},Nat.mod_lt _ (by decide)⟩
def Row (i : Fin {N}) : Prop := ∀ j : Fin {N},
  (pathVertex i = pathVertex j → i=j) ∧
  (i.val<j.val → (Adj (pathVertex i) (pathVertex j) ↔ i.val+1=j.val))
def transitions : Array Nat := #[{', '.join(map(str,s['transitions']))}]
theorem transitions_agree : ∀ i : Fin {N-1},
  (pathVertex ⟨i.val+1,by omega⟩).val = Nat.xor (pathVertex ⟨i.val,by omega⟩).val (2^transitions[i.val]!) := by decide +kernel
theorem minimum_crossings : ∀ k : Fin {n}, {profile['crossings']} ≤ transitions.toList.count k.val := by decide +kernel
theorem displayed_cut_indices : (List.range {N-1}).filter (fun i => transitions[i]! == {profile['coordinate']}) = [{', '.join(map(str,profile['cut_indices']))}] := by decide +kernel
#print axioms transitions_agree
#print axioms minimum_crossings
#print axioms displayed_cut_indices
end {ns}
'''
    (H/'lean'/(data+'.lean')).write_text(src,encoding='utf-8',newline='\n');order.append(data);chunks=[]
    for k,lo in enumerate(range(0,N,width)):
        cnt=min(width,N-lo);module=f'CubeRows{n}_{k:02d}188';chunks.append((module,lo,cnt,k))
        src=f'''import {data}
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace {ns}
theorem rows{k} : ∀ i : Fin {cnt}, Row ⟨{lo}+i.val,by omega⟩ := by decide +kernel
#print axioms rows{k}
end {ns}
'''
        (H/'lean'/(module+'.lean')).write_text(src,encoding='utf-8',newline='\n');order.append(module)
    src='\n'.join('import '+c[0] for c in chunks)+f'\nnamespace {ns}\ntheorem allRows (i : Fin {N}) : Row i := by\n'
    for module,lo,cnt,k in chunks[:-1]:
        src+=f'''  by_cases h{k} : i.val < {lo+cnt}
  · have h := rows{k} ⟨i.val-{lo},by omega⟩
    have he : (⟨{lo}+(i.val-{lo}),by omega⟩ : Fin {N})=i := by apply Fin.ext; simp only [Fin.val_mk]; omega
    simpa only [he] using h
'''
    module,lo,cnt,k=chunks[-1]
    src+=f'''  have h := rows{k} ⟨i.val-{lo},by omega⟩
  have he : (⟨{lo}+(i.val-{lo}),by omega⟩ : Fin {N})=i := by apply Fin.ext; simp only [Fin.val_mk]; omega
  simpa only [he] using h
theorem path_distinct : ∀ i j, pathVertex i = pathVertex j → i=j := by
  intro i j h
  exact (allRows i j).1 h
theorem path_induced : ∀ i j, i.val < j.val → (Adj (pathVertex i) (pathVertex j) ↔ i.val+1=j.val) := by
  intro i j h
  exact (allRows i j).2 h
def path : LayerJoining.InducedPath (Fin {size}) Adj {N-1} := ⟨pathVertex,path_distinct,path_induced⟩
#print axioms allRows
#print axioms path_distinct
#print axioms path_induced
end {ns}
'''
    module=f'Witness{n}188';(H/'lean'/(module+'.lean')).write_text(src,encoding='utf-8',newline='\n');order.append(module)
order.append('Reconstruction7188')
base=json.loads((H/'data/TwoCrossings188-execution.json').read_text());base['new_module_order']=order
base['source_sha256']={n:hashlib.sha256((H/'lean'/(n+'.lean')).read_bytes()).hexdigest() for n in order}
for n in order:
    if (H/'data'/(n+'-audit.json')).exists():continue
    (H/'data'/(n+'-execution.json')).write_text(json.dumps(base,indent=2)+'\n')
(H/'data/current-order.json').write_text(json.dumps(order,indent=2)+'\n')
(H/'scripts/split_witnesses.py').write_bytes(Path(__file__).read_bytes())
print('Split finite pair proofs; planned modules',len(order))
