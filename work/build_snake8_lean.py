import json
from pathlib import Path
vertices=json.loads(Path('outputs/snake8_witness.json').read_text())['vertex_sequence']
source='''import LayerJoining

namespace Snake8
abbrev Vertex := Fin 256
def Adj (u v : Vertex) : Prop :=
  (List.range 8).any (fun k => v.val == Nat.xor u.val (2^k)) = true
instance (u v : Vertex) : Decidable (Adj u v) := inferInstanceAs (Decidable (_ = true))
abbrev Snake := LayerJoining.InducedPath Vertex Adj
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def witnessValues : Array Nat := #[VALUES]
def witnessVertex (i : Fin 99) : Vertex :=
  ⟨witnessValues[i.val]! % 256, Nat.mod_lt _ (by decide)⟩
theorem witness_distinct :
    ∀ i j : Fin 99, witnessVertex i = witnessVertex j → i = j := by decide
theorem witness_induced :
    ∀ i j : Fin 99, i.val < j.val →
      (Adj (witnessVertex i) (witnessVertex j) ↔ i.val+1=j.val) := by decide
def witness : Snake 98 := ⟨witnessVertex, witness_distinct, witness_induced⟩
theorem lower_bound : Nonempty (Snake 98) := ⟨witness⟩
#print axioms witness_distinct
#print axioms witness_induced
#print axioms lower_bound
end Snake8
'''.replace('VALUES',', '.join(map(str,vertices)))
Path('outputs/Snake8.lean').write_text(source,encoding='utf-8')
