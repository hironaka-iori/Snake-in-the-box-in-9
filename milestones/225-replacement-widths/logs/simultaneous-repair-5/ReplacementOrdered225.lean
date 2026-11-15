import LayerJoining
import ReplacementCases225
import ReplacementPairs225

set_option Elab.async false

namespace ReplacementOrdered225
open LayerJoining

theorem ordered_pair {V : Type} {R : V → V → Prop} {n : Nat}
    (p : InducedPath V R n) (q : Fin (n + 1) → V) (a b c d : Nat)
    (ordered : a ≤ b ∧ b ≤ c ∧ c ≤ d ∧ d ≤ n)
    (agreement : ∀ i, ¬(a < i.val ∧ i.val < b) →
      ¬(c < i.val ∧ i.val < d) → q i = p.vertex i)
    (first_distinct : ∀ i j, a ≤ i.val → i.val ≤ b →
      a ≤ j.val → j.val ≤ b → q i = q j → i = j)
    (first_induced : ∀ i j, a ≤ i.val → j.val ≤ b → i.val < j.val →
      (R (q i) (q j) ↔ i.val + 1 = j.val))
    (second_distinct : ∀ i j, c ≤ i.val → i.val ≤ d →
      c ≤ j.val → j.val ≤ d → q i = q j → i = j)
    (second_induced : ∀ i j, c ≤ i.val → j.val ≤ d → i.val < j.val →
      (R (q i) (q j) ↔ i.val + 1 = j.val))
    (first_separated : ∀ i j, (a < i.val ∧ i.val < b) →
      ¬(c < j.val ∧ j.val < d) → (j.val < a ∨ b < j.val) →
      q i ≠ p.vertex j ∧ ¬R (q i) (p.vertex j) ∧ ¬R (p.vertex j) (q i))
    (second_separated : ∀ i j, (c < i.val ∧ i.val < d) →
      ¬(a < j.val ∧ j.val < b) → (j.val < c ∨ d < j.val) →
      q i ≠ p.vertex j ∧ ¬R (q i) (p.vertex j) ∧ ¬R (p.vertex j) (q i))
    (mutual : ∀ i j, (a < i.val ∧ i.val < b) →
      (c < j.val ∧ j.val < d) → q i ≠ q j ∧ ¬R (q i) (q j))
    (i j : Fin (n + 1)) (indices : i.val < j.val) :
    q i ≠ q j ∧ (R (q i) (q j) ↔ i.val + 1 = j.val) :=
  Or.elim
    (ReplacementCases225.classify (a := a) (b := b) (c := c) (d := d)
      (i := i.val) (j := j.val) ordered.2.1 indices)
    (fun h => ReplacementPairs225.local_pair (V := V) (R := R) (n := n)
      q a b first_distinct first_induced i j indices h)
    (fun remaining => Or.elim remaining
      (fun h => ReplacementPairs225.local_pair (V := V) (R := R) (n := n)
        q c d second_distinct second_induced i j indices h)
      (fun remaining => Or.elim remaining
        (fun h => ReplacementPairs225.separated_pair (V := V) (R := R)
          (u := q i) (v := q j) (i := i.val) (j := j.val)
          h.2.2 (mutual i j h.1 h.2.1).1 (mutual i j h.1 h.2.1).2)
        (fun remaining => Or.elim remaining
          (fun h => ReplacementPairs225.right_pair (V := V) (R := R)
            (u := q i) (v := q j) (retained := p.vertex j) (i := i.val) (j := j.val)
            (agreement j h.2.1 h.2.2.1) h.2.2.2.2
            (first_separated i j h.1 h.2.2.1 (Or.inr h.2.2.2.1)))
          (fun remaining => Or.elim remaining
            (fun h => ReplacementPairs225.right_pair (V := V) (R := R)
              (u := q i) (v := q j) (retained := p.vertex j) (i := i.val) (j := j.val)
              (agreement j h.2.1 h.2.2.1) h.2.2.2.2
              (second_separated i j h.1 h.2.1 (Or.inr h.2.2.2.1)))
            (fun remaining => Or.elim remaining
              (fun h => ReplacementPairs225.left_pair (V := V) (R := R)
                (u := q i) (v := q j) (retained := p.vertex i) (i := i.val) (j := j.val)
                (agreement i h.1 h.2.1) h.2.2.2.2
                (first_separated j i h.2.2.1 h.2.1 (Or.inl h.2.2.2.1)))
              (fun remaining => Or.elim remaining
                (fun h => ReplacementPairs225.left_pair (V := V) (R := R)
                  (u := q i) (v := q j) (retained := p.vertex i) (i := i.val) (j := j.val)
                  (agreement i h.1 h.2.1) h.2.2.2.2
                  (second_separated j i h.2.2.1 h.1 (Or.inl h.2.2.2.1)))
                (fun h => ReplacementPairs225.retained_pair (V := V) (R := R) (n := n)
                  p q i j indices (agreement i h.1 h.2.1)
                  (agreement j h.2.2.1 h.2.2.2))))))))

#print axioms ordered_pair
end ReplacementOrdered225
