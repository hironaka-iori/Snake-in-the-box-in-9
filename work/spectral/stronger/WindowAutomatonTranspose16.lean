/-
The delta-swap layout check of WindowAutomatonTranspose for 16-bit fields.

`dsw`, `testBit_dsw`, `swT`, `swP`, `MK`, `pos8`, the per-block lemmas `swT_blk..` and the
512-block check `comp512ok` do not depend on the field width and are shared.  Here the swaps move
whole 16-bit fields (`digit16_dsw`, masks of 65535s `swMask16`, bit shifts `16 * S`), and

  digit16_trans : digit16 (trans16 (512 m) C) (pos8 y) = digit16 C y     (y < 512 m).

Core Lean only.
-/
import WindowAutomatonTranspose
import WindowAutomatonSwar16

namespace Snake9.WindowAutomaton

theorem testBit_digit16' (n l t : Nat) (ht : t < 16) : n.testBit (16 * l + t) = (digit16 n l).testBit t := by
  unfold digit16
  rw [show 65536 ^ l = 2 ^ (16 * l) by simp [Nat.pow_mul], ← Nat.shiftRight_eq_div_pow,
    show (65536 : Nat) = 2 ^ 16 by rfl, Nat.testBit_mod_two_pow, Nat.testBit_shiftRight]
  simp [ht, Nat.add_comm]

theorem field16_ext (a b : Nat) (ha : a < 65536) (hb : b < 65536) (h : ∀ t, t < 16 → a.testBit t = b.testBit t) : a = b := by
  apply Nat.eq_of_testBit_eq
  intro t
  by_cases ht : t < 16
  · exact h t ht
  · have e1 : a.testBit t = false := Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le ha
      (by calc 65536 = 2 ^ 16 := rfl
             _ ≤ 2 ^ t := Nat.pow_le_pow_right (by decide) (by omega)))
    have e2 : b.testBit t = false := Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hb
      (by calc 65536 = 2 ^ 16 := rfl
             _ ≤ 2 ^ t := Nat.pow_le_pow_right (by decide) (by omega)))
    rw [e1, e2]

theorem testBit_field16_mask (M : Bool) (t : Nat) (ht : t < 16) : (if M then 65535 else 0 : Nat).testBit t = M := by
  cases M
  · simp
  · show (65535 : Nat).testBit t = true
    rw [show (65535 : Nat) = 2 ^ 16 - 1 by rfl, Nat.testBit_two_pow_sub_one]; simp [ht]

theorem digit16_dsw (x m S z : Nat) (M : Nat → Bool) (hm : ∀ w, digit16 m w = if M w then 65535 else 0)
    (hd : m &&& (m <<< (16 * S)) = 0) : digit16 (dsw x m (16 * S)) z = digit16 x (swT M S z) := by
  apply field16_ext _ _ (digit16_lt _ _) (digit16_lt _ _)
  intro t ht
  rw [← testBit_digit16' _ _ _ ht, ← testBit_digit16' _ _ _ ht, testBit_dsw _ _ _ _ hd]
  have hb : ∀ w, m.testBit (16 * w + t) = M w := fun w => by
    rw [testBit_digit16' _ _ _ ht, hm w, testBit_field16_mask _ _ ht]
  rw [hb z]
  unfold swT
  by_cases h1 : M z = true
  · simp only [h1, if_true]; congr 1; omega
  · simp only [h1]
    by_cases hs : S ≤ z
    · have e : 16 * z + t - 16 * S = 16 * (z - S) + t := by omega
      rw [e, hb]
      by_cases h2 : M (z - S) = true
      · simp [h2, hs, show 16 * S ≤ 16 * z + t by omega]
      · simp [h2]
    · have hs' : ¬ 16 * S ≤ 16 * z + t := by omega
      simp [hs, hs']

/-- `0xFFFF` on the fields `z < n` with `swP i j z`, by geometric series. -/
def swMask16 (i j n : Nat) : Nat :=
  (65536 ^ 2 ^ i - 1) * 65536 ^ 2 ^ i * ((65536 ^ 2 ^ j - 1) / (65536 ^ 2 ^ (i + 1) - 1)) *
    ((65536 ^ n - 1) / (65536 ^ 2 ^ (j + 1) - 1))

theorem digit16_swMask (i j m z : Nat)
    (h : swMask16 i j (512 * m) = pack16 (tab (fun z => if swP i j z then 65535 else 0) 512) * repK16 512 m) :
    digit16 (swMask16 i j (512 * m)) z = if (decide (z < 512 * m) && swP i j z) then 65535 else 0 := by
  rw [h, ← pack16_tab_rep, digit16_pack _ (tab_bounded _ _ _ (fun _ _ => by split <;> decide))]
  by_cases hz : z < 512 * m
  · rw [tab_getD _ _ _ hz]
    have e : swP i j (z % 512) = swP i j z := by unfold swP; rw [Nat.mod_mod]
    simp [hz, e]
  · have hl : (tab (fun l => (fun z => if swP i j z then 65535 else 0) (l % 512)) (512 * m)).length ≤ z := by
      rw [tab_length]; omega
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none hl]
    simp [hz]

/-- The six delta swaps on 16-bit fields that rotate the nine low index bits of every field by three. -/
def trans16 (n C : Nat) : Nat :=
  dsw (dsw (dsw (dsw (dsw (dsw C (swMask16 0 3 n) (16 * 7)) (swMask16 3 6 n) (16 * 56)) (swMask16 1 4 n) (16 * 14))
    (swMask16 4 7 n) (16 * 112)) (swMask16 2 5 n) (16 * 28)) (swMask16 5 8 n) (16 * 224)

theorem digit16_trans (m C y : Nat) (hy : y < 512 * m)
    (e1 : swMask16 0 3 (512 * m) = pack16 (tab (fun z => if swP 0 3 z then 65535 else 0) 512) * repK16 512 m)
    (e2 : swMask16 3 6 (512 * m) = pack16 (tab (fun z => if swP 3 6 z then 65535 else 0) 512) * repK16 512 m)
    (e3 : swMask16 1 4 (512 * m) = pack16 (tab (fun z => if swP 1 4 z then 65535 else 0) 512) * repK16 512 m)
    (e4 : swMask16 4 7 (512 * m) = pack16 (tab (fun z => if swP 4 7 z then 65535 else 0) 512) * repK16 512 m)
    (e5 : swMask16 2 5 (512 * m) = pack16 (tab (fun z => if swP 2 5 z then 65535 else 0) 512) * repK16 512 m)
    (e6 : swMask16 5 8 (512 * m) = pack16 (tab (fun z => if swP 5 8 z then 65535 else 0) 512) * repK16 512 m)
    (d1 : swMask16 0 3 (512 * m) &&& (swMask16 0 3 (512 * m) <<< (16 * 7)) = 0)
    (d2 : swMask16 3 6 (512 * m) &&& (swMask16 3 6 (512 * m) <<< (16 * 56)) = 0)
    (d3 : swMask16 1 4 (512 * m) &&& (swMask16 1 4 (512 * m) <<< (16 * 14)) = 0)
    (d4 : swMask16 4 7 (512 * m) &&& (swMask16 4 7 (512 * m) <<< (16 * 112)) = 0)
    (d5 : swMask16 2 5 (512 * m) &&& (swMask16 2 5 (512 * m) <<< (16 * 28)) = 0)
    (d6 : swMask16 5 8 (512 * m) &&& (swMask16 5 8 (512 * m) <<< (16 * 224)) = 0) :
    digit16 (trans16 (512 * m) C) (pos8 y) = digit16 C y := by
  unfold trans16
  rw [digit16_dsw _ _ _ _ (MK (512 * m) 5 8) (fun w => digit16_swMask 5 8 m w e6) d6,
    digit16_dsw _ _ _ _ (MK (512 * m) 2 5) (fun w => digit16_swMask 2 5 m w e5) d5,
    digit16_dsw _ _ _ _ (MK (512 * m) 4 7) (fun w => digit16_swMask 4 7 m w e4) d4,
    digit16_dsw _ _ _ _ (MK (512 * m) 1 4) (fun w => digit16_swMask 1 4 m w e3) d3,
    digit16_dsw _ _ _ _ (MK (512 * m) 3 6) (fun w => digit16_swMask 3 6 m w e2) d2,
    digit16_dsw _ _ _ _ (MK (512 * m) 0 3) (fun w => digit16_swMask 0 3 m w e1) d1]
  have hc := allBelowR_spec _ _ comp512ok_eq (y % 512) (Nat.mod_lt _ (by decide))
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hc
  obtain ⟨⟨⟨⟨⟨⟨hp, h6⟩, h5⟩, h4⟩, h3⟩, h2⟩, h1⟩ := hc
  have hh : y / 512 < m := by omega
  have hpos : pos8 y = 512 * (y / 512) + (64 * (y % 512 % 8) + y % 512 / 8 % 64) := by unfold pos8; omega
  rw [hpos, swT_blk58 m _ _ hp hh, swT_blk25 m _ _ h6 hh, swT_blk47 m _ _ h5 hh, swT_blk14 m _ _ h4 hh,
    swT_blk36 m _ _ h3 hh, swT_blk03 m _ _ h2 hh, h1]
  congr 1; omega

end Snake9.WindowAutomaton
