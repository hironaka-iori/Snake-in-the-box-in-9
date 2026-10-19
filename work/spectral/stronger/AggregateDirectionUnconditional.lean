import AggregateDirectionConditional
import AggregateWindowUnconditional
import DirectionWindowBridge

/-!
# The bound 239 from the 145 direction-aware window certificates

`DirectionWindowBridge` (core Lean) derives the three window premises of
`upper_239_of_direction_windows` from `AllRefuted239`, the 145 certificate statements
of `LocalWindowDirKeys`, with the core singleton count `coreAlpha`.  This module
identifies `coreAlpha` with `countSeq` (through `localAlpha_eq_coreAlpha`) and removes
the premises.  The only remaining hypothesis is `AllRefuted239`; the certificate modules
`LocalWindowSat.D*` and `LocalWindowDirSat.allRefuted239_of_unsat` reduce it to the
refutations of the 145 UNSAT cores `LocalWindowCnf.D*`.
-/

namespace Snake9
open SquareIncidence Finset Classical WindowAggregate WindowAutomaton
noncomputable section

theorem countSeq_eq_coreAlpha {m : Nat} (p : Snake m) {k : Nat} (hk : k < m + 1) :
    countSeq p k = LocalWindow.coreAlpha p k := by
  rw [countSeq_eq p k hk, localAlpha_eq_coreAlpha]

theorem sym_eq_symC (a : Nat) : sym a = LocalWindow.symC a := rfl

/-- A snake in Q9 has at most 239 edges, given the 145 direction-aware window
certificates. -/
theorem upper_239_of_refuted (h : LocalWindow.AllRefuted239) {m : Nat} (p : Snake m) :
    m ≤ 239 := by
  obtain ⟨h2, h3, h4⟩ := DirectionWindow.direction_windows_core h p
  apply upper_239_of_direction_windows p
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

#print axioms upper_239_of_refuted
end
end Snake9
