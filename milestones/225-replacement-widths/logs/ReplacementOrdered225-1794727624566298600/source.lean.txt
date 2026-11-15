import ReplacementConditions225
import ReplacementCases225
import ReplacementPairs225

set_option Elab.async false

namespace ReplacementOrdered225
open LayerJoining

theorem ordered_pair {V : Type} {R : V → V → Prop} {n : Nat}
    (p : InducedPath V R n) (q : Fin (n + 1) → V) (a b c d : Nat)
    (conditions : ReplacementConditions225.Conditions p q a b c d)
    (i j : Fin (n + 1)) (indices : i.val < j.val) :
    q i ≠ q j ∧ (R (q i) (q j) ↔ i.val + 1 = j.val) :=
  Or.elim
    (ReplacementCases225.classify (a := a) (b := b) (c := c) (d := d)
      (i := i.val) (j := j.val) conditions.ordered.2.1 indices)
    (fun h => ReplacementPairs225.local_pair (V := V) (R := R) (n := n)
      q a b conditions.first_distinct conditions.first_induced i j indices h)
    (fun remaining => Or.elim remaining
      (fun h => ReplacementPairs225.local_pair (V := V) (R := R) (n := n)
        q c d conditions.second_distinct conditions.second_induced i j indices h)
      (fun remaining => Or.elim remaining
        (fun h => ReplacementPairs225.separated_pair (V := V) (R := R)
          (u := q i) (v := q j) (i := i.val) (j := j.val)
          h.2.2 (conditions.cross_separated i j h.1 h.2.1).1
          (conditions.cross_separated i j h.1 h.2.1).2)
        (fun remaining => Or.elim remaining
          (fun h => ReplacementPairs225.right_pair (V := V) (R := R)
            (u := q i) (v := q j) (retained := p.vertex j) (i := i.val) (j := j.val)
            (conditions.agreement j h.2.1 h.2.2.1) h.2.2.2.2
            (conditions.first_separated i j h.1 h.2.2.1 (Or.inr h.2.2.2.1)))
          (fun remaining => Or.elim remaining
            (fun h => ReplacementPairs225.right_pair (V := V) (R := R)
              (u := q i) (v := q j) (retained := p.vertex j) (i := i.val) (j := j.val)
              (conditions.agreement j h.2.1 h.2.2.1) h.2.2.2.2
              (conditions.second_separated i j h.1 h.2.1 (Or.inr h.2.2.2.1)))
            (fun remaining => Or.elim remaining
              (fun h => ReplacementPairs225.left_pair (V := V) (R := R)
                (u := q i) (v := q j) (retained := p.vertex i) (i := i.val) (j := j.val)
                (conditions.agreement i h.1 h.2.1) h.2.2.2.2
                (conditions.first_separated j i h.2.2.1 h.2.1 (Or.inl h.2.2.2.1)))
              (fun remaining => Or.elim remaining
                (fun h => ReplacementPairs225.left_pair (V := V) (R := R)
                  (u := q i) (v := q j) (retained := p.vertex i) (i := i.val) (j := j.val)
                  (conditions.agreement i h.1 h.2.1) h.2.2.2.2
                  (conditions.second_separated j i h.2.2.1 h.1 (Or.inl h.2.2.2.1)))
                (fun h => ReplacementPairs225.retained_pair (V := V) (R := R) (n := n)
                  p q i j indices (conditions.agreement i h.1 h.2.1)
                  (conditions.agreement j h.2.2.1 h.2.2.2))))))))

#print axioms ordered_pair
end ReplacementOrdered225
