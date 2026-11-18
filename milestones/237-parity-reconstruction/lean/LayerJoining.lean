import Std

namespace LayerJoining

structure InducedPath (V : Type) (R : V → V → Prop) (m : Nat) where
  vertex : Fin (m + 1) → V
  distinct : ∀ i j, vertex i = vertex j → i = j
  induced : ∀ i j, i.val < j.val →
    (R (vertex i) (vertex j) ↔ i.val + 1 = j.val)

/-- The adjacency relation of the Cartesian product with one binary edge. -/
def LayerAdj {V : Type} (R : V → V → Prop) (u v : V × Bool) : Prop :=
  (u.2 = v.2 ∧ R u.1 v.1) ∨ (u.2 ≠ v.2 ∧ u.1 = v.1)

def joinedVertex {V : Type} {R : V → V → Prop} {a b : Nat}
    (p : InducedPath V R a) (q : InducedPath V R b)
    (i : Fin (a + b + 2)) : V × Bool :=
  if h : i.val ≤ a then (p.vertex ⟨i.val, by omega⟩, false)
  else (q.vertex ⟨i.val - (a + 1), by omega⟩, true)

/-- Exact compatibility condition: only the intended terminal pair coincides. -/
def Compatible {V : Type} {R : V → V → Prop} {a b : Nat}
    (p : InducedPath V R a) (q : InducedPath V R b) : Prop :=
  ∀ i j, p.vertex i = q.vertex j ↔ i.val = a ∧ j.val = 0

def join {V : Type} {R : V → V → Prop} {a b : Nat}
    (p : InducedPath V R a) (q : InducedPath V R b)
    (compatible : Compatible p q) : InducedPath (V × Bool) (LayerAdj R) (a + b + 1) where
  vertex := joinedVertex p q
  distinct i j eq := by
    unfold joinedVertex at eq
    split at eq <;> split at eq
    · have h := p.distinct _ _ (congrArg Prod.fst eq)
      apply Fin.ext
      exact congrArg (fun x : Fin (a+1) => x.val) h
    · have h := congrArg Prod.snd eq
      contradiction
    · have h := congrArg Prod.snd eq
      contradiction
    · have h := q.distinct _ _ (congrArg Prod.fst eq)
      have hv := congrArg Fin.val h
      apply Fin.ext
      simp only at hv
      omega
  induced i j hij := by
    unfold joinedVertex
    split <;> split
    · simpa [LayerAdj] using p.induced ⟨i.val, by omega⟩ ⟨j.val, by omega⟩ hij
    · simp only [LayerAdj, Bool.false_eq_true, false_and, ne_eq, not_false_eq_true,
        true_and, false_or]
      rw [compatible]
      simp only [Fin.val_mk]
      omega
    · omega
    · simp only [LayerAdj, true_and, ne_eq, not_true_eq_false, false_and, or_false]
      rw [q.induced ⟨i.val - (a+1), by omega⟩ ⟨j.val - (a+1), by omega⟩ (by simp only; omega)]
      simp only [Fin.val_mk]
      omega

theorem compatibility_necessary {V : Type} {R : V → V → Prop} {a b : Nat}
    (p : InducedPath V R a) (q : InducedPath V R b)
    (h : ∀ i j : Fin (a+b+2), i.val < j.val →
      (LayerAdj R (joinedVertex p q i) (joinedVertex p q j) ↔ i.val+1=j.val)) :
    Compatible p q := by
  intro i j
  have hs := h ⟨i.val, by omega⟩ ⟨a+1+j.val, by omega⟩ (by simp only; omega)
  have hi : i.val ≤ a := by omega
  have hj : ¬ (a+1+j.val ≤ a) := by omega
  simp only [joinedVertex, hi, hj, dite_true, dite_false, Fin.val_mk] at hs
  have he : a+1+j.val-(a+1) = j.val := by omega
  simp only [he, LayerAdj, Bool.false_eq_true, false_and, ne_eq,
    not_false_eq_true, true_and, false_or] at hs
  constructor
  · intro eq
    have hx := hs.mp eq
    omega
  · intro ends
    exact hs.mpr (by omega)

/-- Given the known eight-dimensional bound, these are the only possible
    layer lengths for a single-crossing snake of length 196. -/
theorem lengths_for_196 (a b : Nat) (ha : a ≤ 98) (hb : b ≤ 98)
    (h : a + b + 1 = 196) :
    (a = 98 ∧ b = 97) ∨ (a = 97 ∧ b = 98) := by omega

theorem lengths_for_197 (a b : Nat) (ha : a ≤ 98) (hb : b ≤ 98)
    (h : a + b + 1 = 197) : a = 98 ∧ b = 98 := by omega

theorem single_crossing_upper (a b : Nat) (ha : a ≤ 98) (hb : b ≤ 98) :
    a + b + 1 ≤ 197 := by omega

#print axioms join
#print axioms compatibility_necessary
#print axioms lengths_for_196
#print axioms lengths_for_197
#print axioms single_crossing_upper
end LayerJoining
