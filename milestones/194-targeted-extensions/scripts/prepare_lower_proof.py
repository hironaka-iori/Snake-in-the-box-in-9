from pathlib import Path
import hashlib,json
H=Path(__file__).resolve().parents[1]
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
q=json.loads((H/'data/aligned-lower49.json').read_text())['best'];old=q['old_path'];new=q['path'];cut=q['end']
assert q['start']==0 and len(old)==49 and len(new)==50
modules=['LowerData194']+[f'LowerRows194_{k}' for k in range(7)]+['LowerWitness194']
assert not any((H/'data'/(m+'-audit.json')).exists() for m in modules)
header='set_option maxHeartbeats 0\nset_option maxRecDepth 100000\nnamespace Lower194\n'
data='import LayerJoining\n'+header
data+='def Adj (u v : Fin 128) : Prop := (List.range 7).any (fun k => v.val == Nat.xor u.val (2^k)) = true\n'
data+='instance (u v : Fin 128) : Decidable (Adj u v) := inferInstanceAs (Decidable (_ = true))\n'
for name,values,size in [('old',old,49),('new',new,50)]:
    data+=f'def {name}Values : Array Nat := #['+', '.join(map(str,values))+']\n'
    data+=f'def {name}Vertex (i : Fin {size}) : Fin 128 := ⟨{name}Values[i.val]! % 128,Nat.mod_lt _ (by decide)⟩\n'
    data+=f'def {name}Row (i : Fin {size}) : Prop := ∀ j : Fin {size},\n  ({name}Vertex i={name}Vertex j → i=j) ∧\n  (i.val<j.val → (Adj ({name}Vertex i) ({name}Vertex j) ↔ i.val+1=j.val))\n'
data+=f'theorem retainedOutside : ∀ i : Fin 49, i.val=0 ∨ {cut}≤i.val →\n  newVertex ⟨i.val+1,by omega⟩ = oldVertex i := by decide +kernel\n'
data+='#print axioms retainedOutside\nend Lower194\n'
(H/'lean/LowerData194.lean').write_text(data,encoding='utf-8',newline='\n')
for k in range(7):
    text='import LowerData194\n'+header
    for name,size in [('old',49),('new',50)]:
        count=min(8,size-8*k)
        text+=f'theorem {name}Rows{k} : ∀ i : Fin {count}, {name}Row ⟨{8*k}+i.val,by omega⟩ := by\n  unfold {name}Row\n  decide +kernel\n#print axioms {name}Rows{k}\n'
    text+='end Lower194\n'
    (H/'lean'/f'LowerRows194_{k}.lean').write_text(text,encoding='utf-8',newline='\n')
final=''.join(f'import LowerRows194_{k}\n' for k in range(7))+header
for name,size in [('old',49),('new',50)]:
    final+=f'theorem all{name.title()}Rows (i : Fin {size}) : {name}Row i := by\n'
    for k in range(6):
        final+=f'  by_cases h{k} : i.val < {8*(k+1)}\n  · have h := {name}Rows{k} ⟨i.val-{8*k},by omega⟩\n    have he : (⟨{8*k}+(i.val-{8*k}),by omega⟩ : Fin {size})=i := by apply Fin.ext; simp only [Fin.val_mk]; omega\n    simpa only [he] using h\n'
    final+=f'  have h := {name}Rows6 ⟨i.val-48,by omega⟩\n  have he : (⟨48+(i.val-48),by omega⟩ : Fin {size})=i := by apply Fin.ext; simp only [Fin.val_mk]; omega\n  simpa only [he] using h\n'
    final+=f'def {name}Path : LayerJoining.InducedPath (Fin 128) Adj {size-1} where\n  vertex := {name}Vertex\n  distinct i j h := (all{name.title()}Rows i j).1 h\n  induced i j h := (all{name.title()}Rows i j).2 h\n#print axioms {name}Path\n'
final+='end Lower194\n';(H/'lean/LowerWitness194.lean').write_text(final,encoding='utf-8',newline='\n')
base=json.loads((H/'data/Pruning194-execution.json').read_text());base['new_module_order']=modules
base['source_sha256']={m:sha(H/'lean'/(m+'.lean')) for m in modules}
for p in [H/'data/aligned-lower49.json',H/'data/lower-input.json',H/'data/lower-provenance.json']:base['input_pins'][str(p)]=sha(p)
for m in modules:(H/'data'/(m+'-execution.json')).write_text(json.dumps(base,indent=2)+'\n')
(H/'data/lower-proof-order.json').write_text(json.dumps(modules,indent=2)+'\n')
print('PREPARED_LOWER_PROOF',len(modules))
