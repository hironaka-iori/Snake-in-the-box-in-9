import Std

/- A snake's length is its number of edges. No optimality assumption is declared. -/
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

theorem no192_iff_upperBound :
    (¬ Nonempty (Snake 192)) ↔ (∀ m, Nonempty (Snake m) → m ≤ 191) := by
  constructor
  · intro h m hp
    cases Nat.lt_or_ge m 192 with
    | inl hm => omega
    | inr hm =>
      obtain ⟨p⟩ := hp
      exact False.elim (h ⟨takePrefix p hm⟩)
  · intro h hp
    have := h 192 hp
    omega

/- An exact finite target: 193 distinct cube vertices in induced-path order. -/
def Target192 : Prop :=
  ∃ f : Fin 193 → Vertex,
    (∀ i j, f i = f j → i = j) ∧
    (∀ i j, i.val < j.val → (Adj (f i) (f j) ↔ i.val + 1 = j.val))

theorem target192_iff : Target192 ↔ Nonempty (Snake 192) := by
  constructor
  · rintro ⟨f, hd, hi⟩
    exact ⟨⟨f, hd, hi⟩⟩
  · rintro ⟨p⟩
    exact ⟨p.vertex, p.distinct, p.induced⟩

theorem target192_impossible_iff_upperBound :
    (¬ Target192) ↔ (∀ m, Nonempty (Snake m) → m ≤ 191) := by
  rw [target192_iff, no192_iff_upperBound]

#print axioms no192_iff_upperBound
#print axioms target192_impossible_iff_upperBound

end Snake9
