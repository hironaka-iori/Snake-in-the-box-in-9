import LayerJoining

set_option Elab.async false

namespace TwoBlocks224
open LayerJoining

/-- If two actual induced paths differ only in two ordered open index
intervals, the first replacement alone is induced whenever its new vertices
are disjoint and nonadjacent to the second interval's old vertices. -/
def firstIntermediate {V : Type} {R : V → V → Prop} {n : Nat}
    (p q : InducedPath V R n) (a b c d : Nat)
    (ordered : a ≤ b ∧ b ≤ c ∧ c ≤ d)
    (agreement : ∀ i, ¬(a < i.val ∧ i.val < b) →
      ¬(c < i.val ∧ i.val < d) → q.vertex i = p.vertex i)
    (separation : ∀ i j, (a < i.val ∧ i.val < b) →
      (c < j.val ∧ j.val < d) →
      q.vertex i ≠ p.vertex j ∧ ¬R (q.vertex i) (p.vertex j)) :
    InducedPath V R n where
  vertex i := if a < i.val ∧ i.val < b then q.vertex i else p.vertex i
  distinct i j equal := by
    change (if a < i.val ∧ i.val < b then q.vertex i else p.vertex i) =
      (if a < j.val ∧ j.val < b then q.vertex j else p.vertex j) at equal
    by_cases hi : a < i.val ∧ i.val < b
    · by_cases hj : a < j.val ∧ j.val < b
      · simp only [hi, hj, if_true] at equal
        exact q.distinct i j equal
      · simp only [hi, hj, if_true, if_false] at equal
        by_cases hj_second : c < j.val ∧ j.val < d
        · exact False.elim ((separation i j hi hj_second).1 equal)
        · rw [← agreement j hj hj_second] at equal
          exact q.distinct i j equal
    · by_cases hj : a < j.val ∧ j.val < b
      · simp only [hi, hj, if_true, if_false] at equal
        by_cases hi_second : c < i.val ∧ i.val < d
        · exact False.elim ((separation j i hj hi_second).1 equal.symm)
        · rw [← agreement i hi hi_second] at equal
          exact q.distinct i j equal
      · simp only [hi, hj, if_false] at equal
        exact p.distinct i j equal
  induced i j index_order := by
    change (R (if a < i.val ∧ i.val < b then q.vertex i else p.vertex i)
      (if a < j.val ∧ j.val < b then q.vertex j else p.vertex j) ↔
      i.val + 1 = j.val)
    by_cases hi : a < i.val ∧ i.val < b
    · by_cases hj : a < j.val ∧ j.val < b
      · simp only [hi, hj, if_true]
        exact q.induced i j index_order
      · simp only [hi, hj, if_true, if_false]
        by_cases hj_second : c < j.val ∧ j.val < d
        · have no_edge := (separation i j hi hj_second).2
          constructor
          · intro edge
            exact False.elim (no_edge edge)
          · intro consecutive
            have blocks_order := ordered.2.1
            omega
        · rw [← agreement j hj hj_second]
          exact q.induced i j index_order
    · by_cases hj : a < j.val ∧ j.val < b
      · simp only [hi, hj, if_true, if_false]
        have hi_second : ¬(c < i.val ∧ i.val < d) := by
          have blocks_order := ordered.2.1
          omega
        rw [← agreement i hi hi_second]
        exact q.induced i j index_order
      · simp only [hi, hj, if_false]
        exact p.induced i j index_order

#print axioms firstIntermediate
end TwoBlocks224
