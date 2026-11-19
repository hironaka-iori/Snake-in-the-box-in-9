import Std

/- A snake's length is its number of edges. No optimality axiom is declared. -/
namespace Snake9

abbrev Vertex := Fin 512

def Adj (u v : Vertex) : Prop :=
  (List.range 9).any (fun k => v.val == Nat.xor u.val (2 ^ k)) = true

instance (u v : Vertex) : Decidable (Adj u v) :=
  inferInstanceAs (Decidable (_ = true))

theorem adj_iff_coordinate_flip (u v : Vertex) :
    Adj u v ↔ ∃ k : Nat, k < 9 ∧ v.val = Nat.xor u.val (2 ^ k) := by
  simp [Adj, List.any_eq_true]

structure Snake (m : Nat) where
  vertex : Fin (m + 1) → Vertex
  distinct : ∀ i j, vertex i = vertex j → i = j
  induced : ∀ i j, i.val < j.val → (Adj (vertex i) (vertex j) ↔ i.val + 1 = j.val)

def takePrefix {m k : Nat} (p : Snake m) (h : k ≤ m) : Snake k where
  vertex i := p.vertex ⟨i.val, by omega⟩
  distinct i j eq := by
    have e := p.distinct ⟨i.val, by omega⟩ ⟨j.val, by omega⟩ eq
    apply Fin.ext
    exact congrArg (fun x : Fin (m + 1) => x.val) e
  induced i j hij := p.induced ⟨i.val, by omega⟩ ⟨j.val, by omega⟩ hij

end Snake9
