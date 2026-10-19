import AggregateDirection237Conditional
import AggregateDirectionUnconditional
import DirectionWindowBridge5R4b

/-!
# The bound 237 from the 387 five-centre window certificates

`DirectionWindowBridge5R4b` (core Lean) derives the four window premises of
`upper_237_of_direction_windows5R4b` from `AllRefuted237`, the 387 certificate statements
of `LocalWindowDirKeysR4b`, with the core singleton count `coreAlpha`.  This module
identifies `coreAlpha` with `countSeq` (through `localAlpha_eq_coreAlpha`) and removes
the premises.  The only remaining hypothesis is `AllRefuted237`; the certificate modules
`LocalWindowSat.D*` and `LocalWindowDirSatR4b.allRefuted237_of_unsat` reduce it to the
refutations of the 387 UNSAT cores `LocalWindowCnf.D*`.
-/

namespace Snake9
open SquareIncidence Finset Classical WindowAggregate WindowAutomaton
noncomputable section

/-- A snake in Q9 has at most 237 edges, given the 387 five-centre window
certificates. -/
theorem upper_237_of_refuted (h : LocalWindow.AllRefuted237) {m : Nat} (p : Snake m) :
    m ≤ 237 := by
  obtain ⟨h2, h3, h4, h5⟩ := DirectionWindow5R4b.direction_windows_core5 h p
  apply upper_237_of_direction_windows5R4b p
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

#print axioms upper_237_of_refuted
end
end Snake9
