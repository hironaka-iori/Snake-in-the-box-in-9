import Floors233Main
import LocalWindowDirUnsat6SB233
import LocalWindowShareUnsat6SB233

/-!
# Unconditional bound 233

The share-weighted six-centre chain `B233` (milestones 31 and 33):
`Snake9.Floors233Port.upper_233_of_certs6SB233` (`Floors233Main`: the automaton `B233`, the share
identity and main's five share floors) has the two certificate obligations as its only premises.
They are discharged here by the kernel-checked certificates of
`milestones/33-233-lean/certify/cert233.py`:

* `allRefuted6SB233 : AllRefuted6SB233` (`LocalWindowDirUnsat6SB233`): the plain k6 keys
  (reused from the sets of the bounds 237, 236 and 235, or new: each from its own certificate or
  from the widened certificate of its seed by L1/L2 of `LocalWindowFamilies`) and the H8 keys;
* `allRefutedShare6SB233 : AllRefutedShare6SB233` (`LocalWindowShareUnsat6SB233`): the share
  thresholds `RefutedShare (winOf ds) (boundsOf syms) 12 K`.
-/

namespace Snake9

theorem upper_bound_233 {m : Nat} (p : Snake m) : m ≤ 233 :=
  Floors233Port.upper_233_of_certs6SB233 LocalWindow.allRefuted6SB233 LocalWindow.allRefutedShare6SB233 p

theorem verified_interval_191_233 :
    Nonempty (Snake 191) ∧ ∀ m, Nonempty (Snake m) → m ≤ 233 := by
  refine ⟨lower_bound, ?_⟩
  rintro m ⟨p⟩
  exact upper_bound_233 p

end Snake9

#print axioms Snake9.upper_bound_233
#print axioms Snake9.verified_interval_191_233
