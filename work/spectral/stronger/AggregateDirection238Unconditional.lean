import AggregateDirection238Conditional
import AggregateDirectionUnconditional
import DirectionWindowBridge5

/-!
# The bound 238 from the 325 five-centre window certificates

`DirectionWindowBridge5` (core Lean) derives the four window premises of
`upper_238_of_direction_windows5` from `AllRefuted238`, the 325 certificate statements
of `LocalWindowDirKeys5`, with the core singleton count `coreAlpha`.  This module
identifies `coreAlpha` with `countSeq` (through `localAlpha_eq_coreAlpha`) and removes
the premises.  The only remaining hypothesis is `AllRefuted238`; the certificate modules
`LocalWindowSat.D*` and `LocalWindowDirSat5.allRefuted238_of_unsat` reduce it to the
refutations of the 325 UNSAT cores `LocalWindowCnf.D*`.
-/

namespace Snake9
open SquareIncidence Finset Classical WindowAggregate WindowAutomaton
noncomputable section

/-- A snake in Q9 has at most 238 edges, given the 325 five-centre window
certificates. -/
theorem upper_238_of_refuted (h : LocalWindow.AllRefuted238) {m : Nat} (p : Snake m) :
    m ≤ 238 := by
  obtain ⟨h2, h3, h4, h5⟩ := DirectionWindow5.direction_windows_core5 h p
  apply upper_238_of_direction_windows5 p
  · intro j hj
    rw [countSeq_eq_coreAlpha p (by omega), countSeq_eq_coreAlpha p (by omega)]
    exact h2 j hj
  · intro j hj
    rw [countSeq_eq_coreAlpha p (by omega), countSeq_eq_coreAlpha p (by omega),
      countSeq_eq_coreAlpha p (by omega)]
    exact h3 j hj
  · intro j hj
    rw [countSeq_eq_coreAlpha p (by omega), countSeq_eq_coreAlpha p (by omega),
      countSeq_eq_coreAlpha p (by omega), countSeq_eq_coreAlpha p (by omega)]
    exact h4 j hj
  · intro j hj
    rw [countSeq_eq_coreAlpha p (by omega), countSeq_eq_coreAlpha p (by omega),
      countSeq_eq_coreAlpha p (by omega), countSeq_eq_coreAlpha p (by omega),
      countSeq_eq_coreAlpha p (by omega)]
    exact h5 j hj

#print axioms upper_238_of_refuted
end
end Snake9
