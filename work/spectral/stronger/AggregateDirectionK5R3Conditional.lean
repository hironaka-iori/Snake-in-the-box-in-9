import WindowAutomatonK5R3Sequence
import AggregateDirectionConditional

namespace Snake9
open SquareIncidence Finset Classical WindowAggregate WindowAutomaton
noncomputable section
set_option maxHeartbeats 1600000

theorem winK5R3_eq (p : Snake m) (i : Nat) : winK5R3 (pathDir p) i = blockList p i 8 := rfl

/-- Conditional 238-edge bound: no window of 2..5 consecutive internal vertices has a
direction shape and lumped counts listed in `forbMaskK5R3` (325 certified exclusions,
radius 3).  The premise is NOT proved in Lean; the unconditional bound remains 245. -/
theorem upper_238_of_direction_windowsK5R3 {m : Nat} (p : Snake m)
    (hw2 : ∀ j, j + 3 ≤ m → wforbK5R3 [pathDir p j, pathDir p (j+1), pathDir p (j+2)]
      [sym (countSeq p (j+1)), sym (countSeq p (j+2))] = false)
    (hw3 : ∀ j, j + 4 ≤ m → wforbK5R3 [pathDir p j, pathDir p (j+1), pathDir p (j+2), pathDir p (j+3)]
      [sym (countSeq p (j+1)), sym (countSeq p (j+2)), sym (countSeq p (j+3))] = false)
    (hw4 : ∀ j, j + 5 ≤ m → wforbK5R3 [pathDir p j, pathDir p (j+1), pathDir p (j+2), pathDir p (j+3), pathDir p (j+4)]
      [sym (countSeq p (j+1)), sym (countSeq p (j+2)), sym (countSeq p (j+3)), sym (countSeq p (j+4))] = false)
    (hw5 : ∀ j, j + 6 ≤ m → wforbK5R3 [pathDir p j, pathDir p (j+1), pathDir p (j+2), pathDir p (j+3), pathDir p (j+4), pathDir p (j+5)]
      [sym (countSeq p (j+1)), sym (countSeq p (j+2)), sym (countSeq p (j+3)), sym (countSeq p (j+4)), sym (countSeq p (j+5))] = false) : m ≤ 238 := by
  by_cases hm : m < 7
  · omega
  obtain ⟨h0, h1, hpos, _, hid⟩ := countSeq_facts p (by omega)
  have hpos' : ∀ j, 1 ≤ j → j + 1 ≤ m → 1 ≤ countSeq p j := by
    intro j hj hjm
    have := hpos (j - 1) (by omega)
    simpa [show j - 1 + 1 = j by omega] using this
  have htot := total_boundK5R3 (pathDir p) (countSeq p) m (by omega) hpos'
    (fun i hi => by rw [winK5R3_eq]; exact snake_inducedPattern_block p i 8 hi) hw2 hw3 hw4 hw5
  rw [sumA_eq_psum] at htot
  omega

#print axioms upper_238_of_direction_windowsK5R3
end
end Snake9
