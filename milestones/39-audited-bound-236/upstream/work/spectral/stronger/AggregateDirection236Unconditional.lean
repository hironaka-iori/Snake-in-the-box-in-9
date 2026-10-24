import AggregateDirection236Conditional
import AggregateDirectionUnconditional
import DirectionWindowBridge5R4

/-!
# The bound 236 from the 732 five-centre window certificates

`DirectionWindowBridge5R4` (core Lean) derives the four window premises of
`upper_236_of_direction_windows5R4` from `AllRefuted236`, the 732 certificate statements
of `LocalWindowDirKeysR4`, with the core singleton count `coreAlpha`.  This module
identifies `coreAlpha` with `countSeq` (through `localAlpha_eq_coreAlpha`) and removes
the premises.  The only remaining hypothesis is `AllRefuted236`; the certificate modules
`LocalWindowSat.D*` and `LocalWindowDirSatR4.allRefuted236_of_unsat` reduce it to the
refutations of the 732 UNSAT cores `LocalWindowCnf.D*`.
-/

namespace Snake9
open SquareIncidence Finset Classical WindowAggregate WindowAutomaton
noncomputable section

/-- A snake in Q9 has at most 236 edges, given the 732 five-centre window
certificates. -/
theorem upper_236_of_refuted (h : LocalWindow.AllRefuted236) {m : Nat} (p : Snake m) :
    m ≤ 236 := by
  obtain ⟨h2, h3, h4, h5⟩ := DirectionWindow5R4.direction_windows_core5 h p
  apply upper_236_of_direction_windows5R4 p
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

#print axioms upper_236_of_refuted
end
end Snake9
