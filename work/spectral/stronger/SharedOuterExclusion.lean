import SharedFiniteReduction
import SharedMissingHoleWrappers
import SharedCentralDoubleExclusion
import SharedCrossStars
import SharedCrossedStars
import SharedCrossStarExclusion
import SharedSwitchExclusion
import SharedOrdinaryFork

namespace Snake9
open SquareIncidence Finset Classical
noncomputable section

theorem SharedOuterConfig.impossible {m : Nat} {p : Snake m} {a b c d : Coord}
    (h : SharedOuterConfig p a b c d) (f : MissingAtNeighbor p a b)
    (hFcard : f.F.card=2) : False := by
  obtain ⟨u,w,hu,hw,huw,hcases⟩ := h.finite_cases f hFcard
  have huR := (Finset.mem_sdiff.mp hu).1
  have hwR := (Finset.mem_sdiff.mp hw).1
  have hun : u≠h.e ∧ u≠h.x ∧ u≠h.y := by
    simpa only [Finset.mem_insert,Finset.mem_singleton,not_or] using (Finset.mem_sdiff.mp hu).2
  have hwn : w≠h.e ∧ w≠h.x ∧ w≠h.y := by
    simpa only [Finset.mem_insert,Finset.mem_singleton,not_or] using (Finset.mem_sdiff.mp hw).2
  simp only [SharedFiniteResidual,Matrix.cons_val_zero,Matrix.cons_val_succ] at hcases
  rcases hcases with h01 | h02 | h03 | h04 | h05 | h06 | h07 | h08 | h09 | h10 |
    h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20
  · exact h.cd_ce_false f h01
  · exact h.cd_de_false f h02
  · exact h.ce_de_false f h03
  · exact h.cx_dy_false f h04
  · exact h.cy_dx_false f h05
  · exact h.cx_B_false f h06
  · exact h.dx_B_false f h07
  · exact h.cy_A_false f h08
  · exact h.dy_A_false f h09
  · exact h.cr_xy_false f h.e h.he h.hex h.hey h10
  · exact h.cr_xy_false f u huR hun.2.1 hun.2.2 h11
  · exact h.cr_xy_false f w hwR hwn.2.1 hwn.2.2 h12
  · exact h.dr_xy_false f h.e h.he h.hex h.hey h13
  · exact h.dr_xy_false f u huR hun.2.1 hun.2.2 h14
  · exact h.dr_xy_false f w hwR hwn.2.1 hwn.2.2 h15
  · exact h.A_B_false f h16
  · exact h.A_xy_false f h17
  · exact h.B_xy_false f h18
  · exact h.switch_family_false f u huR hun.1 hun.2.1 hun.2.2 h19
  · exact h.switch_family_false f w hwR hwn.1 hwn.2.1 hwn.2.2 h20

#print axioms SharedOuterConfig.impossible
end
end Snake9
