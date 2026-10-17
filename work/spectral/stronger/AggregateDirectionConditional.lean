import WindowAutomatonBridge
import AggregateWindowConditional

namespace Snake9
open SquareIncidence Finset Classical WindowAggregate WindowAutomaton
noncomputable section
set_option maxHeartbeats 1600000

theorem sumA_eq_psum (a : Nat → Nat) : ∀ n, sumA a n = psum (fun j => a (j+1)) n
  | 0 => rfl
  | n + 1 => by simp [sumA, psum, sumA_eq_psum a n]

/-- Conditional 239-edge bound from the direction-aware automaton.

The premises say that no window of two, three or four consecutive internal
vertices has a direction shape and lumped singleton counts (`sym`) listed in
the certified exclusion table `forbMask` (145 entries, each with a drat-trim
certificate for the radius-three local model; see
`milestones/10-window-aggregate/`).  `pathDir p j` is the coordinate flipped by
the `j`-th edge and `countSeq p j` is the singleton count at vertex `j`.  The
premises are NOT proved in Lean, so the unconditional bound remains 245. -/
theorem upper_239_of_direction_windows {m : Nat} (p : Snake m)
    (hw2 : ∀ j, j + 3 ≤ m → wforb [pathDir p j, pathDir p (j+1), pathDir p (j+2)]
      [sym (countSeq p (j+1)), sym (countSeq p (j+2))] = false)
    (hw3 : ∀ j, j + 4 ≤ m → wforb [pathDir p j, pathDir p (j+1), pathDir p (j+2), pathDir p (j+3)]
      [sym (countSeq p (j+1)), sym (countSeq p (j+2)), sym (countSeq p (j+3))] = false)
    (hw4 : ∀ j, j + 5 ≤ m →
      wforb [pathDir p j, pathDir p (j+1), pathDir p (j+2), pathDir p (j+3), pathDir p (j+4)]
      [sym (countSeq p (j+1)), sym (countSeq p (j+2)), sym (countSeq p (j+3)),
        sym (countSeq p (j+4))] = false) : m ≤ 239 := by
  by_cases hm : m < 6
  · omega
  obtain ⟨h0, h1, hpos, _, hid⟩ := countSeq_facts p (by omega)
  have hpos' : ∀ j, 1 ≤ j → j + 1 ≤ m → 1 ≤ countSeq p j := by
    intro j hj hjm
    have := hpos (j - 1) (by omega)
    simpa [show j - 1 + 1 = j by omega] using this
  have htot := total_bound (pathDir p) (countSeq p) m (by omega) hpos'
    (fun i hi => snake_inducedPattern p i hi) hw2 hw3 hw4
  rw [sumA_eq_psum] at htot
  omega

#print axioms upper_239_of_direction_windows
end
end Snake9
