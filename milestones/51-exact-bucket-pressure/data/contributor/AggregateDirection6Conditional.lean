import DirectionWindowBridge6
import AggregateDirectionUnconditional

/-!
# Bounds from a six-centre automaton (generic in the tables and the certificate keys)

`upper_of_windows6`: for any table bundle `T : Tables6` whose step test is kernel-checked
(`StepOK T`, from the 204 shards of a generated data module), the five window premises
(`Windows6`, windows of 3 to 7 directions with the singleton counts `countSeq`) give

  `(num + 35 den) m + 6 den ≤ 9171 den + 7 num + (2^bits - 1)`.

The constant is the five-centre one (`gen_lean_chain5.py`): seven leading steps, six
leading counts at least 1, the potential bound `2^bits - 1`, and the incidence identity
`c₀ + Σ c_j + c_m + 35 (m+1) ≤ 9214` with endpoint counts at least 4.

`upper_of_refuted6` removes the premises: `DirectionWindowBridge6.direction_windows_core6`
derives them from the certificate statements `AllRefutedList keys`, given the two kernel
checks `keysOK6 keys` and `Cover6 T keys`, and `countSeq_eq_coreAlpha` identifies the
counts.  A generated module `AggregateDirection6<T>` then only reads off `m ≤ N`.
-/

namespace Snake9
open SquareIncidence Finset Classical WindowAggregate WindowAutomaton
noncomputable section
set_option maxHeartbeats 1600000

theorem win8s6_eq (p : Snake m) (i : Nat) : win8s6 (pathDir p) i = blockList p i 8 := rfl

theorem upper_of_windows6 (T : Tables6) (hT : StepOK T) {m : Nat} (p : Snake m)
    (hw : Windows6 T (pathDir p) (countSeq p) m) :
    (T.num + 35 * T.den) * m + 6 * T.den ≤ 9171 * T.den + 7 * T.num + (2 ^ T.bits - 1) := by
  by_cases hm : m < 7
  · have : (T.num + 35 * T.den) * m ≤ (T.num + 35 * T.den) * 6 := Nat.mul_le_mul_left _ (by omega)
    omega
  obtain ⟨h0, h1, hpos, _, hid⟩ := countSeq_facts p (by omega)
  have hpos' : ∀ j, 1 ≤ j → j + 1 ≤ m → 1 ≤ countSeq p j := by
    intro j hj hjm
    have := hpos (j - 1) (by omega)
    simpa [show j - 1 + 1 = j by omega] using this
  have htot := total_bound6 T hT (pathDir p) (countSeq p) m (by omega) hpos'
    (fun i hi => by rw [win8s6_eq]; exact snake_inducedPattern_block p i 8 hi) hw
  rw [sumA_eq_psum] at htot
  have hps : psum (fun j => countSeq p (j + 1)) (m - 1) + 35 * m ≤ 9171 := by omega
  have hmul := Nat.mul_le_mul_left T.den hps
  rw [Nat.mul_add] at hmul
  have e : (T.num + 35 * T.den) * m = T.num * m + T.den * (35 * m) := by
    rw [Nat.add_mul, Nat.mul_assoc, Nat.mul_left_comm]
  rw [e]
  omega

/-- The bound from the certificate statements of the keys, for any covered table. -/
theorem upper_of_refuted6 (T : Tables6) (keys : List (List Nat × List Nat))
    (h : LocalWindow.AllRefutedList keys) (hv : DirectionWindow6.keysOK6 keys = true)
    (hc : DirectionWindow6.Cover6 T keys) (hT : StepOK T) {m : Nat} (p : Snake m) :
    (T.num + 35 * T.den) * m + 6 * T.den ≤ 9171 * T.den + 7 * T.num + (2 ^ T.bits - 1) := by
  have hw := DirectionWindow6.direction_windows_core6 h hv hc p
  apply upper_of_windows6 T hT p
  refine ⟨fun j hj => ?_, fun j hj => ?_, fun j hj => ?_, fun j hj => ?_, fun j hj => ?_⟩
  · rw [countSeq_eq_coreAlpha p (by omega), countSeq_eq_coreAlpha p (by omega)]
    exact hw.w2 j hj
  · rw [countSeq_eq_coreAlpha p (by omega), countSeq_eq_coreAlpha p (by omega),
      countSeq_eq_coreAlpha p (by omega)]
    exact hw.w3 j hj
  · rw [countSeq_eq_coreAlpha p (by omega), countSeq_eq_coreAlpha p (by omega),
      countSeq_eq_coreAlpha p (by omega), countSeq_eq_coreAlpha p (by omega)]
    exact hw.w4 j hj
  · rw [countSeq_eq_coreAlpha p (by omega), countSeq_eq_coreAlpha p (by omega),
      countSeq_eq_coreAlpha p (by omega), countSeq_eq_coreAlpha p (by omega),
      countSeq_eq_coreAlpha p (by omega)]
    exact hw.w5 j hj
  · rw [countSeq_eq_coreAlpha p (by omega), countSeq_eq_coreAlpha p (by omega),
      countSeq_eq_coreAlpha p (by omega), countSeq_eq_coreAlpha p (by omega),
      countSeq_eq_coreAlpha p (by omega), countSeq_eq_coreAlpha p (by omega)]
    exact hw.w6 j hj

#print axioms upper_of_windows6
#print axioms upper_of_refuted6
end
end Snake9
