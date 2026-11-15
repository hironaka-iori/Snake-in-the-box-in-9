import LayerJoining

set_option Elab.async false

namespace ReplacementPairs225
open LayerJoining

theorem local_pair {V : Type} {R : V → V → Prop} {n : Nat}
    (q : Fin (n + 1) → V) (a b : Nat)
    (distinct : ∀ i j, a ≤ i.val → i.val ≤ b →
      a ≤ j.val → j.val ≤ b → q i = q j → i = j)
    (induced : ∀ i j, a ≤ i.val → j.val ≤ b → i.val < j.val →
      (R (q i) (q j) ↔ i.val + 1 = j.val))
    (i j : Fin (n + 1)) (indices : i.val < j.val)
    (bounds : a ≤ i.val ∧ j.val ≤ b) :
    q i ≠ q j ∧ (R (q i) (q j) ↔ i.val + 1 = j.val) := by
  refine ⟨?_, induced i j bounds.1 bounds.2 indices⟩
  intro equal
  have same := distinct i j bounds.1
    (Nat.le_trans (Nat.le_of_lt indices) bounds.2)
    (Nat.le_trans bounds.1 (Nat.le_of_lt indices)) bounds.2 equal
  exact (Nat.ne_of_lt indices) (congrArg Fin.val same)

theorem separated_pair {V : Type} {R : V → V → Prop} {u v : V} {i j : Nat}
    (gap : i + 1 ≠ j) (distinct : u ≠ v) (no_edge : ¬R u v) :
    u ≠ v ∧ (R u v ↔ i + 1 = j) :=
  ⟨distinct, ⟨fun h => False.elim (no_edge h),
    fun h => False.elim (gap h)⟩⟩

theorem right_pair {V : Type} {R : V → V → Prop} {u v retained : V} {i j : Nat}
    (same : v = retained) (gap : i + 1 ≠ j)
    (separated : u ≠ retained ∧ ¬R u retained ∧ ¬R retained u) :
    u ≠ v ∧ (R u v ↔ i + 1 = j) := by
  subst v
  exact separated_pair gap separated.1 separated.2.1

theorem left_pair {V : Type} {R : V → V → Prop} {u v retained : V} {i j : Nat}
    (same : u = retained) (gap : i + 1 ≠ j)
    (separated : v ≠ retained ∧ ¬R v retained ∧ ¬R retained v) :
    u ≠ v ∧ (R u v ↔ i + 1 = j) := by
  subst u
  exact separated_pair gap (fun h => separated.1 h.symm) separated.2.2

theorem retained_pair {V : Type} {R : V → V → Prop} {n : Nat}
    (p : InducedPath V R n) (q : Fin (n + 1) → V)
    (i j : Fin (n + 1)) (indices : i.val < j.val)
    (left_same : q i = p.vertex i) (right_same : q j = p.vertex j) :
    q i ≠ q j ∧ (R (q i) (q j) ↔ i.val + 1 = j.val) := by
  rw [left_same, right_same]
  refine ⟨?_, p.induced i j indices⟩
  intro equal
  exact (Nat.ne_of_lt indices) (congrArg Fin.val (p.distinct i j equal))

#print axioms local_pair
#print axioms separated_pair
#print axioms right_pair
#print axioms left_pair
#print axioms retained_pair
end ReplacementPairs225
