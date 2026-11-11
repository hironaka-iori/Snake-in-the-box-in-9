from pathlib import Path
import json,hashlib
R=Path('E:/Snake-in-a-box');H=R/'milestones/188-dimensional-constructions'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
(H/'lean/LayerJoining.lean').write_bytes((R/'work/final_lean/LayerJoining.lean').read_bytes())
(H/'lean/TwoCrossings188.lean').write_bytes(Path('D:/Codex/2026-10-13/new-chat/work/TwoCrossings188.lean').read_bytes())
seeds=json.loads((H/'data/lower-dimensional-seeds.json').read_text())
order=['LayerJoining','TwoCrossings188']
def pathdecl(name,vs,n):
    L=len(vs)-1
    return f'''def {name}Values : Array Nat := #[{', '.join(map(str,vs))}]
def {name}Vertex (i : Fin {L+1}) : Fin {1<<n} :=
  ⟨{name}Values[i.val]! % {1<<n},Nat.mod_lt _ (by decide)⟩
theorem {name}_distinct : ∀ i j, {name}Vertex i = {name}Vertex j → i=j := by decide +kernel
theorem {name}_induced : ∀ i j, i.val < j.val → (Adj ({name}Vertex i) ({name}Vertex j) ↔ i.val+1=j.val) := by decide +kernel
def {name} : LayerJoining.InducedPath (Fin {1<<n}) Adj {L} := ⟨{name}Vertex,{name}_distinct,{name}_induced⟩
#print axioms {name}_distinct
#print axioms {name}_induced
'''
for n in [6,7,8]:
    j=seeds[str(n)];L=j['edges'];profile=j['profiles'][0];name=f'Witness{n}188';order.append(name)
    src=f'''import LayerJoining
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Dimensional188.Witness{n}
def Adj (u v : Fin {1<<n}) : Prop := (List.range {n}).any (fun k => v.val == Nat.xor u.val (2^k)) = true
instance (u v : Fin {1<<n}) : Decidable (Adj u v) := inferInstanceAs (Decidable (_ = true))
'''+pathdecl('path',j['vertices'],n)+f'''
def transitions : Array Nat := #[{', '.join(map(str,j['transitions']))}]
theorem transitions_agree : ∀ i : Fin {L},
  (pathVertex ⟨i.val+1,by omega⟩).val = Nat.xor (pathVertex ⟨i.val,by omega⟩).val (2^transitions[i.val]!) := by decide +kernel
theorem minimum_crossings : ∀ k : Fin {n}, {profile['crossings']} ≤ transitions.toList.count k.val := by decide +kernel
theorem displayed_cut_indices : (List.range {L}).filter (fun i => transitions[i]! == {profile['coordinate']}) = [{', '.join(map(str,profile['cut_indices']))}] := by decide +kernel
#print axioms transitions_agree
#print axioms minimum_crossings
#print axioms displayed_cut_indices
end Dimensional188.Witness{n}
'''
    (H/'lean'/(name+'.lean')).write_text(src,encoding='utf-8',newline='\n')
profile=seeds['7']['profiles'][0]
src='''import TwoCrossings188
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Dimensional188.Reconstruction7
open LayerJoining
def Adj (u v : Fin 64) : Prop := (List.range 6).any (fun k => v.val == Nat.xor u.val (2^k)) = true
instance (u v : Fin 64) : Decidable (Adj u v) := inferInstanceAs (Decidable (_ = true))
'''
for name,part in zip(['p','q','r'],profile['parts']):src+=pathdecl(name,part['path'],6)
src+='''theorem pq : Compatible p q := by decide +kernel
theorem qr : Compatible q r := by decide +kernel
theorem pr : ∀ i j, p.vertex i ≠ r.vertex j ∧ ¬ Adj (p.vertex i) (r.vertex j) := by decide +kernel
def reconstructed : InducedPath (Fin 64 × Bool) (LayerAdj Adj) 50 := twoCrossings p q r pq qr pr
#print axioms pq
#print axioms qr
#print axioms pr
#print axioms reconstructed
end Dimensional188.Reconstruction7
'''
name='Reconstruction7188';order.append(name);(H/'lean'/(name+'.lean')).write_text(src,encoding='utf-8',newline='\n')
pins={str(p):sha(p) for p in [H/'sources/minortriad-index.html',H/'data/lower-dimensional-seeds.json',H/'scripts/native_resources.py']}
plan={'new_module_order':order,'source_sha256':{n:sha(H/'lean'/(n+'.lean')) for n in order},'input_pins':pins,
      'lean_bin':'D:/Codex/2026-10-01/it-should-have-a-property-of/work/lean-research/lean-4.19.0-windows/bin',
      'search_paths':[str(H/'build')],'checker_sha256':sha(H/'scripts/check_core.py')}
for n in order:(H/'data'/(n+'-execution.json')).write_text(json.dumps(plan,indent=2)+'\n')
(H/'data/current-order.json').write_text(json.dumps(order,indent=2)+'\n')
(H/'scripts/prepare_lean.py').write_bytes(Path(__file__).read_bytes())
print('Prepared',order)
