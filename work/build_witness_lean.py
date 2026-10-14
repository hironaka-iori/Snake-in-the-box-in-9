import json
from pathlib import Path

p = Path('outputs/Snake9.lean')
base = p.read_text(encoding='utf-8').split('-- BEGIN WITNESS')[0].removesuffix('end Snake9\n')
vertices = json.loads(Path('outputs/snake9_witness.json').read_text())['vertex_sequence']
code = '''-- BEGIN WITNESS
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def witnessValues : Array Nat := #[VALUES]

def witnessVertex (i : Fin 192) : Vertex :=
  ⟨witnessValues[i.val]! % 512, Nat.mod_lt _ (by decide)⟩

theorem witness_distinct :
    ∀ i j : Fin 192, witnessVertex i = witnessVertex j → i = j := by decide

theorem witness_induced :
    ∀ i j : Fin 192, i.val < j.val →
      (Adj (witnessVertex i) (witnessVertex j) ↔ i.val + 1 = j.val) := by decide

def witness : Snake 191 := ⟨witnessVertex, witness_distinct, witness_induced⟩

theorem lower_bound : Nonempty (Snake 191) := ⟨witness⟩

theorem optimality_of_no192 (h : ¬ Target192) :
    Nonempty (Snake 191) ∧ (∀ m, Nonempty (Snake m) → m ≤ 191) :=
  ⟨lower_bound, target192_impossible_iff_upperBound.mp h⟩

#print axioms witness_distinct
#print axioms witness_induced
#print axioms lower_bound
#print axioms optimality_of_no192
end Snake9
'''.replace('VALUES', ', '.join(map(str, vertices)))
p.write_text(base+code, encoding='utf-8')
