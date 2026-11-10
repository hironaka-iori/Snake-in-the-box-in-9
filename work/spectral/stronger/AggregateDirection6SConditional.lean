import ShareBridge
import DirectionWindowBridge6S
import CombinedShareToy

/-!
# Bounds from a share-weighted six-centre automaton (generic in the tables and the keys)

The glue of the 233 route (milestones/28-combined-identities, milestones/31-233-cost,
milestones/33-233-lean).  For any table bundle `T : Tables6S` whose step test is kernel-checked
(`StepOK6S T`, from 204 shards):

1. **Telescoping.** `total_bound6S` gives
   `num (m - 7) ≤ den Σ_{n < m-7} (120 sym a(n+7) + S5 n) + (2^bits - 1)`.
2. **Window bounds.** `S5 n ≤ Σ_{j=n+3}^{n+7} coreShare 12 p j` (`share_windows6S`, from the
   share certificates and the floor theorems).
3. **Share identity.** `core_charge_sum_le 12 p` (`ShareBridge`):
   `Σ_{k ≤ m} (24 coreAlpha p k + coreShare 12 p k) + 840 (m+1) ≤ 221136`, turned into the
   `Combined.rsum` form by `rsum_eq_sum`.
4. **Combination.** `Combined.combined_bound` (milestones/28-combined-identities/lean/
   CombinedShareToy.lean) with `sym ≤ α`, `4 ≤ α 0`, `4 ≤ α m`, `1 ≤ α j` (`countSeq_facts`):

   `(num + 4200 den) m ≤ 1099800 den + 7 num + (2^bits - 1)`.

With `num/den = 520/1` and `bits = 10` this is `4720 m ≤ 1104463`, so `m ≤ 233`.

`upper_of_refuted6S` takes the certificate statements (`AllRefutedList` of the plain k6 keys
and of the H8 keys, `AllRefutedShareList` of the share thresholds), the floor theorems of
origin/main (`Floors233`) and the kernel checks (`keysOK6`, `Cover6`, `keysOKH8`, `CoverH8`,
`ShareCover`, `StepOK6S`).
-/

namespace Snake9
open SquareIncidence Finset Classical WindowAggregate WindowAutomaton LocalWindow
  DirectionWindow6 DirectionWindow6S
noncomputable section
set_option maxHeartbeats 1600000

/-- The sum adapter: `Combined.rsum` is the sum over `Finset.range`. -/
theorem rsum_eq_sum (f : Nat → Nat) : ∀ n, Combined.rsum f n = ∑ k ∈ Finset.range n, f k
  | 0 => by simp [Combined.rsum]
  | n + 1 => by rw [Finset.sum_range_succ, ← rsum_eq_sum f n]; rfl

/-- The bound from the window premises and the share window bounds. -/
theorem upper_of_windows6S (T : Tables6S) (hT : StepOK6S T) {m : Nat} (p : Snake m)
    (hw : Windows6S T (pathDir p) (coreAlpha p) m)
    (hS : (∀ j, 1 ≤ j → j + 1 ≤ m → 1 ≤ coreAlpha p j) → ∀ n, n + 8 ≤ m →
      share6 T [pathDir p (n+2), pathDir p (n+3), pathDir p (n+4), pathDir p (n+5),
          pathDir p (n+6), pathDir p (n+7)]
        [sym (coreAlpha p (n+3)), sym (coreAlpha p (n+4)), sym (coreAlpha p (n+5)),
          sym (coreAlpha p (n+6)), sym (coreAlpha p (n+7))] ≤
        coreShare 12 p (n+3) + coreShare 12 p (n+4) + coreShare 12 p (n+5) +
          coreShare 12 p (n+6) + coreShare 12 p (n+7)) :
    (T.k6.num + 4200 * T.k6.den) * m ≤ 1099800 * T.k6.den + 7 * T.k6.num + (2 ^ T.k6.bits - 1) := by
  by_cases hm : m < 7
  · have : (T.k6.num + 4200 * T.k6.den) * m ≤ (T.k6.num + 4200 * T.k6.den) * 6 :=
      Nat.mul_le_mul_left _ (by omega)
    omega
  obtain ⟨h0, h1, hpos, _, _⟩ := countSeq_facts p (by omega)
  have hpos' : ∀ j, 1 ≤ j → j + 1 ≤ m → 1 ≤ coreAlpha p j := by
    intro j hj hjm
    have := hpos (j - 1) (by omega)
    rw [show j - 1 + 1 = j by omega, countSeq_eq_coreAlpha_le p j (by omega)] at this
    exact this
  have htel := total_bound6S T hT (pathDir p) (coreAlpha p) m (by omega) hpos'
    (fun i hi => snake_inducedPattern_block p i 8 hi) hw
  have hid := core_charge_sum_le 12 p (by omega)
  rw [← rsum_eq_sum] at hid
  rw [countSeq_eq_coreAlpha_le p 0 (by omega)] at h0
  rw [countSeq_eq_coreAlpha_le p m (by omega)] at h1
  exact Combined.combined_bound T.k6.num T.k6.den (2 ^ T.k6.bits - 1) m (coreAlpha p)
    (coreShare 12 p) (fun j => sym (coreAlpha p j))
    (fun n => share6 T [pathDir p (n+2), pathDir p (n+3), pathDir p (n+4), pathDir p (n+5),
          pathDir p (n+6), pathDir p (n+7)]
        [sym (coreAlpha p (n+3)), sym (coreAlpha p (n+4)), sym (coreAlpha p (n+5)),
          sym (coreAlpha p (n+6)), sym (coreAlpha p (n+7))])
    (by omega) htel (fun n hn => hS hpos' n (by omega)) (fun j => sym_le _) hpos' h0 h1 hid

/-- The bound from the certificate statements, the floor theorems and the kernel checks. -/
theorem upper_of_refuted6S (T : Tables6S) (keys hkeys : List (List Nat × List Nat))
    (skeys : List (List Nat × List Nat × Nat))
    (h : AllRefutedList keys) (hh : AllRefutedList hkeys) (hs : AllRefutedShareList skeys)
    (hF : Floors233)
    (hv : keysOK6 keys = true) (hc : Cover6 T.k6 keys)
    (hvh : keysOKH8 hkeys = true) (hch : CoverH8 T hkeys)
    (hcs : ShareCover T skeys) (hT : StepOK6S T) {m : Nat} (p : Snake m) :
    (T.k6.num + 4200 * T.k6.den) * m ≤ 1099800 * T.k6.den + 7 * T.k6.num + (2 ^ T.k6.bits - 1) :=
  upper_of_windows6S T hT p (direction_windows_core6S h hv hc hh hvh hch p)
    (fun hpos n hn => share_windows6S p hF hs hcs hpos n hn)

/-- The arithmetic of the 233 instance: `λ = 520/1`, 10-bit potential. -/
theorem m_le_233_of (m : Nat) (h : (520 + 4200 * 1) * m ≤ 1099800 * 1 + 7 * 520 + (2 ^ 10 - 1)) :
    m ≤ 233 := by
  omega

#print axioms rsum_eq_sum
#print axioms upper_of_windows6S
#print axioms upper_of_refuted6S
#print axioms m_le_233_of
end
end Snake9
