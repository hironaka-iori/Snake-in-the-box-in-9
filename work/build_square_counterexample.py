from pathlib import Path
import json

root=Path(__file__).resolve().parents[1]
data=json.loads((root/'outputs/square_local_n9_a1_path_d2.json').read_text())
vertices=data['path'];m=len(vertices)-1;i=vertices.index(0)
assert m==137 and i==127
transitions=[(u^v).bit_length()-1 for u,v in zip(vertices,vertices[1:])]
witness={'dimension':9,'edges':m,'initial_vertex':vertices[0],
 'vertex_sequence':vertices,'transition_sequence':transitions,
 'distinguished_index':i,'distinguished_vertex':0,'singleton_coordinate_pairs':[[2,3]],
 'endpoint_hamming_distances':[vertices[0].bit_count(),vertices[-1].bit_count()]}
(root/'outputs/square_counterexample.json').write_text(json.dumps(witness,indent=2))

source=r'''import Snake9

namespace SquareCounterexample
open Snake9
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- The three other vertices of the coordinate square are outside the path. -/
def SingletonSquare {m : Nat} (p : Snake m) (i : Fin (m+1)) (a b : Nat) : Prop :=
  a < 9 ∧ b < 9 ∧ a < b ∧
  ∀ j, (p.vertex j).val ≠ Nat.xor (p.vertex i).val (2^a) ∧
    (p.vertex j).val ≠ Nat.xor (p.vertex i).val (2^b) ∧
    (p.vertex j).val ≠ Nat.xor (Nat.xor (p.vertex i).val (2^a)) (2^b)

instance {m : Nat} (p : Snake m) (i : Fin (m+1)) (a b : Nat) :
    Decidable (SingletonSquare p i a b) := by unfold SingletonSquare; infer_instance

def coordinatePairs : List (Nat × Nat) :=
  (List.range 9).flatMap (fun a => (List.range 9).map (fun b => (a,b)))

def singletonPairs {m : Nat} (p : Snake m) (i : Fin (m+1)) : List (Nat × Nat) :=
  coordinatePairs.filter (fun ab => decide (SingletonSquare p i ab.1 ab.2))

theorem mem_singletonPairs_iff {m : Nat} (p : Snake m) (i : Fin (m+1)) (a b : Nat) :
    (a,b) ∈ singletonPairs p i ↔ SingletonSquare p i a b := by
  have hp : (a,b) ∈ coordinatePairs ↔ a < 9 ∧ b < 9 := by
    simp [coordinatePairs, List.mem_flatMap, List.mem_map]
  simp only [singletonPairs, List.mem_filter, decide_eq_true_eq]
  rw [hp]
  constructor
  · exact fun h => h.2
  · exact fun h => ⟨⟨h.1,h.2.1⟩,h⟩

def witnessValues : Array Nat := #[VERTICES]
def witnessVertex (i : Fin 138) : Vertex :=
  ⟨witnessValues[i.val]! % 512, Nat.mod_lt _ (by decide)⟩

theorem witness_distinct :
    ∀ i j : Fin 138, witnessVertex i = witnessVertex j → i = j := by decide
theorem witness_induced :
    ∀ i j : Fin 138, i.val < j.val →
      (Adj (witnessVertex i) (witnessVertex j) ↔ i.val+1=j.val) := by decide

def witness : Snake 137 := ⟨witnessVertex,witness_distinct,witness_induced⟩
def centerIndex : Fin 138 := ⟨127,by decide⟩

theorem center_and_endpoints :
    (witness.vertex centerIndex).val = 0 ∧
    (witness.vertex ⟨0,by decide⟩).val = 145 ∧
    (witness.vertex ⟨137,by decide⟩).val = 288 := by decide

theorem center_is_internal : 0 < centerIndex.val ∧ centerIndex.val < 137 := by decide
theorem center_ten_edges_from_ends : 10 ≤ centerIndex.val ∧ centerIndex.val+10 ≤ 137 := by decide

theorem exactly_one_singleton_square : singletonPairs witness centerIndex = [(2,3)] := by decide

theorem unique_square_characterization (a b : Nat) :
    SingletonSquare witness centerIndex a b ↔ a=2 ∧ b=3 := by
  rw [← mem_singletonPairs_iff, exactly_one_singleton_square]
  simp

theorem universal_internal_two_square_claim_false :
    ¬ (∀ m (p : Snake m) (i : Fin (m+1)),
      0 < i.val → i.val < m → 2 ≤ (singletonPairs p i).length) := by
  intro h
  have hc := h 137 witness centerIndex center_is_internal.1 center_is_internal.2
  rw [exactly_one_singleton_square] at hc
  contradiction

#print axioms witness_distinct
#print axioms witness_induced
#print axioms exactly_one_singleton_square
#print axioms unique_square_characterization
#print axioms universal_internal_two_square_claim_false
end SquareCounterexample
'''.replace('VERTICES',', '.join(map(str,vertices)))
for destination in ['work/final_lean/SquareCounterexample.lean','outputs/SquareCounterexample.lean']:
    (root/destination).write_text(source,encoding='utf-8')
print('Generated explicit 137-edge witness and Lean square-counterexample module.')
