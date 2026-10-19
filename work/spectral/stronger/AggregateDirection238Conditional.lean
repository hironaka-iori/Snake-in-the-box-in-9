import WindowAutomaton5Sequence
import AggregateDirectionConditional

namespace Snake9
open SquareIncidence Finset Classical WindowAggregate WindowAutomaton
noncomputable section
set_option maxHeartbeats 1600000

theorem win8_eq (p : Snake m) (i : Nat) : win8 (pathDir p) i = blockList p i 8 := rfl

/-- Conditional 238-edge bound from the five-centre direction-aware automaton (the
exclusion masks `forbMaskOf5` of `WindowAutomaton5Data`).  Same premise shape as
`upper_239_of_direction_windows`, with windows of up to five consecutive internal
vertices.  `AggregateDirection238Unconditional` discharges the premises from the window
certificates. -/
theorem upper_238_of_direction_windows5 {m : Nat} (p : Snake m)
    (hw2 : ∀ j, j + 3 ≤ m → wforb5 [pathDir p j, pathDir p (j+1), pathDir p (j+2)]
      [sym (countSeq p (j+1)), sym (countSeq p (j+2))] = false)
    (hw3 : ∀ j, j + 4 ≤ m → wforb5 [pathDir p j, pathDir p (j+1), pathDir p (j+2), pathDir p (j+3)]
      [sym (countSeq p (j+1)), sym (countSeq p (j+2)), sym (countSeq p (j+3))] = false)
    (hw4 : ∀ j, j + 5 ≤ m →
      wforb5 [pathDir p j, pathDir p (j+1), pathDir p (j+2), pathDir p (j+3), pathDir p (j+4)]
      [sym (countSeq p (j+1)), sym (countSeq p (j+2)), sym (countSeq p (j+3)),
        sym (countSeq p (j+4))] = false)
    (hw5 : ∀ j, j + 6 ≤ m →
      wforb5 [pathDir p j, pathDir p (j+1), pathDir p (j+2), pathDir p (j+3), pathDir p (j+4),
        pathDir p (j+5)]
      [sym (countSeq p (j+1)), sym (countSeq p (j+2)), sym (countSeq p (j+3)),
        sym (countSeq p (j+4)), sym (countSeq p (j+5))] = false) : m ≤ 238 := by
  by_cases hm : m < 7
  · omega
  obtain ⟨h0, h1, hpos, _, hid⟩ := countSeq_facts p (by omega)
  have hpos' : ∀ j, 1 ≤ j → j + 1 ≤ m → 1 ≤ countSeq p j := by
    intro j hj hjm
    have := hpos (j - 1) (by omega)
    simpa [show j - 1 + 1 = j by omega] using this
  have htot := total_bound5 (pathDir p) (countSeq p) m (by omega) hpos'
    (fun i hi => by rw [win8_eq]; exact snake_inducedPattern_block p i 8 hi) hw2 hw3 hw4 hw5
  rw [sumA_eq_psum] at htot
  omega

#print axioms upper_238_of_direction_windows5
end
end Snake9
