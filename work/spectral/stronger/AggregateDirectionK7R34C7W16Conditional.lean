import WindowAutomatonK7R34C7W16Sequence
import AggregateDirectionConditional

namespace Snake9
open SquareIncidence Finset Classical WindowAggregate WindowAutomaton
noncomputable section
set_option maxHeartbeats 1600000

theorem winK7R34C7W16_eq (p : Snake m) (i : Nat) : winK7R34C7W16 (pathDir p) i = blockList p i 9 := rfl

/-- Conditional 231-edge bound: no window of 2..7 consecutive internal vertices has a
direction shape and lumped counts listed in the tables of `WindowAutomatonK7R34C7W16Data`
(58817 certified exclusions, radius 3/4).  The premise is NOT proved in Lean; the
unconditional bound remains 245. -/
theorem upper_231_of_direction_windowsK7R34C7W16 {m : Nat} (p : Snake m)
    (hw2 : ∀ j, j + 3 ≤ m → wforbK7R34C7W16 [pathDir p j, pathDir p (j+1), pathDir p (j+2)]
      [symK 8 (countSeq p (j+1)), symK 8 (countSeq p (j+2))] = false)
    (hw3 : ∀ j, j + 4 ≤ m → wforbK7R34C7W16 [pathDir p j, pathDir p (j+1), pathDir p (j+2), pathDir p (j+3)]
      [symK 8 (countSeq p (j+1)), symK 8 (countSeq p (j+2)), symK 8 (countSeq p (j+3))] = false)
    (hw4 : ∀ j, j + 5 ≤ m → wforbK7R34C7W16 [pathDir p j, pathDir p (j+1), pathDir p (j+2), pathDir p (j+3), pathDir p (j+4)]
      [symK 8 (countSeq p (j+1)), symK 8 (countSeq p (j+2)), symK 8 (countSeq p (j+3)), symK 8 (countSeq p (j+4))] = false)
    (hw5 : ∀ j, j + 6 ≤ m → wforbK7R34C7W16 [pathDir p j, pathDir p (j+1), pathDir p (j+2), pathDir p (j+3), pathDir p (j+4), pathDir p (j+5)]
      [symK 8 (countSeq p (j+1)), symK 8 (countSeq p (j+2)), symK 8 (countSeq p (j+3)), symK 8 (countSeq p (j+4)), symK 8 (countSeq p (j+5))] = false)
    (hw6 : ∀ j, j + 7 ≤ m → wforbK7R34C7W16 [pathDir p j, pathDir p (j+1), pathDir p (j+2), pathDir p (j+3), pathDir p (j+4), pathDir p (j+5), pathDir p (j+6)]
      [symK 8 (countSeq p (j+1)), symK 8 (countSeq p (j+2)), symK 8 (countSeq p (j+3)), symK 8 (countSeq p (j+4)), symK 8 (countSeq p (j+5)), symK 8 (countSeq p (j+6))] = false)
    (hw7 : ∀ j, j + 8 ≤ m → wforbK7R34C7W16 [pathDir p j, pathDir p (j+1), pathDir p (j+2), pathDir p (j+3), pathDir p (j+4), pathDir p (j+5), pathDir p (j+6), pathDir p (j+7)]
      [symK 8 (countSeq p (j+1)), symK 8 (countSeq p (j+2)), symK 8 (countSeq p (j+3)), symK 8 (countSeq p (j+4)), symK 8 (countSeq p (j+5)), symK 8 (countSeq p (j+6)), symK 8 (countSeq p (j+7))] = false) : m ≤ 231 := by
  by_cases hm : m < 8
  · omega
  obtain ⟨h0, h1, hpos, _, hid⟩ := countSeq_facts p (by omega)
  have hpos' : ∀ j, 1 ≤ j → j + 1 ≤ m → 1 ≤ countSeq p j := by
    intro j hj hjm
    have := hpos (j - 1) (by omega)
    simpa [show j - 1 + 1 = j by omega] using this
  have htot := total_boundK7R34C7W16 (pathDir p) (countSeq p) m (by omega) hpos'
    (fun i hi => by rw [winK7R34C7W16_eq]; exact snake_inducedPattern_block p i 9 hi) hw2 hw3 hw4 hw5 hw6 hw7
  rw [sumA_eq_psum] at htot
  omega

#print axioms upper_231_of_direction_windowsK7R34C7W16
end
end Snake9
