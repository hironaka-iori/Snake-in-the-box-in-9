import D239Shape
import D239Refs
import AggregateDirectionConditional
import UpperBound241
/-!
# No flagged direction window occurs in a snake of `Q_9`; hence every snake has at most 239 edges

`upper_239_of_direction_windows` (AggregateDirectionConditional) assumes that no window of two,
three or four consecutive internal vertices has a direction shape and lumped counts flagged in
the automaton table `forbMask` (`wforb`).  `D239Shape.no_w2/3/4` discharge these premises: shape
case split and cube normalisation (forwards or backwards), the kernel-decided link from the table
to the 145 certified range tuples (`D239Table`), and their refutations (`D239Refs`).
-/
namespace Snake9

/-- **Unconditional bound**: every snake in the 9-cube has at most 239 edges. -/
theorem upper_bound_239 {m : Nat} (p : Snake m) : m ≤ 239 :=
  upper_239_of_direction_windows p (fun j hj => D239.no_w2 D239.ref_012 D239.tab_012 p j hj)
    (fun j hj => D239.no_w3 D239.ref_0120 D239.ref_0123 D239.tab_0120 D239.tab_0123 p j hj)
    (fun j hj => D239.no_w4 D239.ref_01203 D239.ref_01230 D239.ref_01234 D239.tab_01203
      D239.tab_01230 D239.tab_01234 D239.tab_01231 p j hj)

theorem upper_bound_239' : ∀ m, Nonempty (Snake m) → m ≤ 239 :=
  fun _ ⟨p⟩ => upper_bound_239 p

/-- The verified interval: a 191-edge snake exists, and no snake has more than 239 edges. -/
theorem verified_interval_191_239 :
    Nonempty (Snake 191) ∧ ∀ m, Nonempty (Snake m) → m ≤ 239 :=
  ⟨lower_bound, upper_bound_239'⟩

end Snake9

#print axioms Snake9.upper_bound_239
#print axioms Snake9.verified_interval_191_239
