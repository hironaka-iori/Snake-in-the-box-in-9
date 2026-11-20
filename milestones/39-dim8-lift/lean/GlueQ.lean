import Glue2
import CubeBridgeQ
/-! The glue for the parent-pointer cube CNF. -/
set_option linter.deprecated false
namespace Dim8Lift.Sym
open Dim8Lift Dim8Lift.Cube Snake9.LocalWindow

/-- **Glue.** Cube UNSATs for every representative and the cover statement give `NoPit 13 L 64`. -/
theorem noPit_of_cubesQ {L : Nat} (reps : List (Nat × Nat)) (h113 : 113 ≤ L) (h255 : L ≤ 255)
    (hcov : CoverOK L reps) (hcubes : ∀ r ∈ reps, Unsat (cubeCnfQ 13 L r.2 r.1)) : NoPit 13 L 64 := by
  intro S ℓ hp
  obtain ⟨w, hw, hcnt⟩ := move_max S
  have hp1 := pit_word w hw hp
  have hm1 := maxSub_word w hw (maxSub_kmax S)
  have hk := kmax_ge S h113 hp.card
  obtain ⟨w2, hw2, r, hr, hrk, hA⟩ := hcov _ _ _ hp1 hk hm1 hcnt
  have hp2 := pit_word w2 hw2 hp1
  have hm2 := maxSub_word w2 hw2 hm1
  rw [← hrk] at hm2
  exact no_pit_of_unsatQ (hcubes r hr) (by omega) h255 (by omega) hp2 hA (hsub_of_max hm2)

end Dim8Lift.Sym

#print axioms Dim8Lift.Sym.noPit_of_cubesQ
