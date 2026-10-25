import DirectionWindowBridge7
import AggregateDirectionUnconditional

/-!
# Bounds from a seven-centre automaton (generic in the tables and the certificate keys)

`upper_of_windows7`: for any table bundle `T : Tables7` whose step test is kernel-checked
(`StepOK7 T`, from the shards of a generated data module), the window premises
(`Windows7`: the k6 windows of 3 to 7 directions, the F8 windows and the H9 windows, with
the singleton counts `countSeq`) give

  `(num + 35 den) m + 7 den ≤ 9171 den + 8 num + (2^bits - 1)`.

This is the six-centre constant with one more step of memory: eight leading steps, seven
leading counts at least 1 (`total_bound7`), and the incidence identity
`c₀ + Σ c_j + c_m + 35 (m+1) ≤ 9214` with endpoint counts at least 4.  With
`num/den = 4516/1083` and 13 bits it reads `42421 m + 7581 ≤ 9976512`, i.e. `m ≤ 234`.

`upper_of_refuted7` removes the premises: `DirectionWindowBridge7.direction_windows_core7`
derives them from the certificate statements of the k6/F8 keys and of the H9 keys, given
the kernel checks `keysOK6`, `Cover7`, `keysOKH` and `CoverH`.
-/

namespace Snake9
open SquareIncidence Finset Classical WindowAggregate WindowAutomaton
noncomputable section
set_option maxHeartbeats 1600000

theorem win9s7_eq (p : Snake m) (i : Nat) : win9s7 (pathDir p) i = blockList p i 9 := rfl

theorem upper_of_windows7 (T : Tables7) (hT : StepOK7 T) {m : Nat} (p : Snake m)
    (hw : Windows7 T (pathDir p) (countSeq p) m) :
    (T.num + 35 * T.den) * m + 7 * T.den ≤ 9171 * T.den + 8 * T.num + (2 ^ T.bits - 1) := by
  by_cases hm : m < 8
  · have : (T.num + 35 * T.den) * m ≤ (T.num + 35 * T.den) * 7 := Nat.mul_le_mul_left _ (by omega)
    omega
  obtain ⟨h0, h1, hpos, _, hid⟩ := countSeq_facts p (by omega)
  have hpos' : ∀ j, 1 ≤ j → j + 1 ≤ m → 1 ≤ countSeq p j := by
    intro j hj hjm
    have := hpos (j - 1) (by omega)
    simpa [show j - 1 + 1 = j by omega] using this
  have htot := total_bound7 T hT (pathDir p) (countSeq p) m (by omega) hpos'
    (fun i hi => by rw [win9s7_eq]; exact snake_inducedPattern_block p i 9 hi) hw
  rw [sumA_eq_psum] at htot
  have hps : psum (fun j => countSeq p (j + 1)) (m - 1) + 35 * m ≤ 9171 := by omega
  have hmul := Nat.mul_le_mul_left T.den hps
  rw [Nat.mul_add] at hmul
  have e : (T.num + 35 * T.den) * m = T.num * m + T.den * (35 * m) := by
    rw [Nat.add_mul, Nat.mul_assoc, Nat.mul_left_comm]
  rw [e]
  omega

/-- The bound from the certificate statements of the k6/F8 keys `keys` and the H9 keys
`hkeys`, for any covered table. -/
theorem upper_of_refuted7 (T : Tables7) (keys hkeys : List (List Nat × List Nat))
    (h : LocalWindow.AllRefutedList keys) (hv : DirectionWindow6.keysOK6 keys = true)
    (hc : DirectionWindow7.Cover7 T keys)
    (hh : LocalWindow.AllRefutedList hkeys) (hvh : DirectionWindow7.keysOKH hkeys = true)
    (hch : DirectionWindow7.CoverH T hkeys) (hT : StepOK7 T) {m : Nat} (p : Snake m) :
    (T.num + 35 * T.den) * m + 7 * T.den ≤ 9171 * T.den + 8 * T.num + (2 ^ T.bits - 1) := by
  have hw := DirectionWindow7.direction_windows_core7 h hv hc hh hvh hch p
  apply upper_of_windows7 T hT p
  refine ⟨⟨fun j hj => ?_, fun j hj => ?_, fun j hj => ?_, fun j hj => ?_, fun j hj => ?_⟩,
    fun j hj => ?_, fun j hj => ?_⟩
  · rw [countSeq_eq_coreAlpha p (by omega), countSeq_eq_coreAlpha p (by omega)]
    exact hw.w6.w2 j hj
  · rw [countSeq_eq_coreAlpha p (by omega), countSeq_eq_coreAlpha p (by omega),
      countSeq_eq_coreAlpha p (by omega)]
    exact hw.w6.w3 j hj
  · rw [countSeq_eq_coreAlpha p (by omega), countSeq_eq_coreAlpha p (by omega),
      countSeq_eq_coreAlpha p (by omega), countSeq_eq_coreAlpha p (by omega)]
    exact hw.w6.w4 j hj
  · rw [countSeq_eq_coreAlpha p (by omega), countSeq_eq_coreAlpha p (by omega),
      countSeq_eq_coreAlpha p (by omega), countSeq_eq_coreAlpha p (by omega),
      countSeq_eq_coreAlpha p (by omega)]
    exact hw.w6.w5 j hj
  · rw [countSeq_eq_coreAlpha p (by omega), countSeq_eq_coreAlpha p (by omega),
      countSeq_eq_coreAlpha p (by omega), countSeq_eq_coreAlpha p (by omega),
      countSeq_eq_coreAlpha p (by omega), countSeq_eq_coreAlpha p (by omega)]
    exact hw.w6.w6 j hj
  · rw [countSeq_eq_coreAlpha p (by omega), countSeq_eq_coreAlpha p (by omega),
      countSeq_eq_coreAlpha p (by omega), countSeq_eq_coreAlpha p (by omega),
      countSeq_eq_coreAlpha p (by omega), countSeq_eq_coreAlpha p (by omega),
      countSeq_eq_coreAlpha p (by omega)]
    exact hw.w7 j hj
  · rw [countSeq_eq_coreAlpha p (by omega), countSeq_eq_coreAlpha p (by omega),
      countSeq_eq_coreAlpha p (by omega), countSeq_eq_coreAlpha p (by omega),
      countSeq_eq_coreAlpha p (by omega), countSeq_eq_coreAlpha p (by omega),
      countSeq_eq_coreAlpha p (by omega)]
    exact hw.wh j hj

#print axioms upper_of_windows7
#print axioms upper_of_refuted7
end
end Snake9
