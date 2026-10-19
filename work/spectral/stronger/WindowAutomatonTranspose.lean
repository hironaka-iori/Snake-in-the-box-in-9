/-
Layout transposition for the 8-symbol (lump cap 7) SWAR chains, checked with six delta swaps.

The generated Data module stores every shape's potential twice: `potC` in code order and `potT`
with the three newest base-8 digits of the code rotated (`pos8`), so that one packed comparison
covers all transitions of a shape pair.  The earlier check compared the two layouts field by
field (32,768 kernel iterations per shape, about 16 s).  Here the rotation of the nine low index
bits of every field is undone by six delta swaps, each a transposition of two index bits:

  dsw x m s = x ^^^ t ^^^ (t <<< s),  t = ((x >>> s) ^^^ x) &&& m

exchanges bit `p` with bit `p + s` wherever `m` has bit `p` set (`testBit_dsw`, given that `m`
and `m <<< s` are disjoint).  With byte-uniform masks (`swMask`, a product of geometric series
the kernel evaluates with a few big-number operations) a swap moves whole fields
(`digit_dsw`).  `digit_trans8` composes the six swaps and shows

  potT = trans8 n potC   ->   digit potT (pos8 y) = digit potC y   for every y < n,

so each shape costs one kernel equality of big numbers instead of a loop.

Core Lean only.
-/
import WindowAutomatonSwar

namespace Snake9.WindowAutomaton

/-- Delta swap: exchanges bit `p` with bit `p + s` wherever `m` has bit `p` set. -/
def dsw (x m s : Nat) : Nat :=
  let t := ((x >>> s) ^^^ x) &&& m
  x ^^^ t ^^^ (t <<< s)

theorem testBit_dsw (x m s p : Nat) (hd : m &&& (m <<< s) = 0) :
    (dsw x m s).testBit p = if m.testBit p then x.testBit (p + s)
      else if s ≤ p ∧ m.testBit (p - s) = true then x.testBit (p - s) else x.testBit p := by
  have hdp : (m &&& (m <<< s)).testBit p = false := by rw [hd]; exact Nat.zero_testBit p
  simp only [Nat.testBit_and, Nat.testBit_shiftLeft] at hdp
  unfold dsw
  simp only [Nat.testBit_xor, Nat.testBit_and, Nat.testBit_shiftLeft, Nat.testBit_shiftRight]
  rw [Nat.add_comm s p]
  by_cases hs : s ≤ p
  · have e : s + (p - s) = p := by omega
    have hge : decide (p ≥ s) = true := by simp; omega
    simp only [e, hge] at hdp ⊢
    generalize m.testBit p = a at hdp ⊢
    generalize m.testBit (p - s) = b at hdp ⊢
    generalize x.testBit p = c
    generalize x.testBit (p + s) = d
    generalize x.testBit (p - s) = f
    cases a <;> cases b <;> cases c <;> cases d <;> cases f <;> simp_all
  · have hge : decide (p ≥ s) = false := by simp; omega
    simp only [hge] at hdp ⊢
    generalize m.testBit p = a at hdp ⊢
    generalize x.testBit p = c
    generalize x.testBit (p + s) = d
    cases a <;> cases c <;> cases d <;> simp_all <;> intro h <;> omega

theorem testBit_digit8 (n l t : Nat) (ht : t < 8) : n.testBit (8 * l + t) = (digit n l).testBit t := by
  unfold digit
  rw [show 256 ^ l = 2 ^ (8 * l) by simp [Nat.pow_mul], ← Nat.shiftRight_eq_div_pow,
    show (256 : Nat) = 2 ^ 8 by rfl, Nat.testBit_mod_two_pow, Nat.testBit_shiftRight]
  simp [ht, Nat.add_comm]

theorem byte_ext (a b : Nat) (ha : a < 256) (hb : b < 256) (h : ∀ t, t < 8 → a.testBit t = b.testBit t) : a = b := by
  apply Nat.eq_of_testBit_eq
  intro t
  by_cases ht : t < 8
  · exact h t ht
  · have e1 : a.testBit t = false := Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le ha
      (by calc 256 = 2 ^ 8 := rfl
             _ ≤ 2 ^ t := Nat.pow_le_pow_right (by decide) (by omega)))
    have e2 : b.testBit t = false := Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hb
      (by calc 256 = 2 ^ 8 := rfl
             _ ≤ 2 ^ t := Nat.pow_le_pow_right (by decide) (by omega)))
    rw [e1, e2]

theorem testBit_byte_mask (M : Bool) (t : Nat) (ht : t < 8) : (if M then 255 else 0 : Nat).testBit t = M := by
  cases M
  · simp
  · show (255 : Nat).testBit t = true
    rw [show (255 : Nat) = 2 ^ 8 - 1 by rfl, Nat.testBit_two_pow_sub_one]; simp [ht]

/-- Field index after one byte-field delta swap. -/
def swT (M : Nat → Bool) (S z : Nat) : Nat :=
  if M z then z + S else if S ≤ z ∧ M (z - S) = true then z - S else z

theorem digit_dsw (x m S z : Nat) (M : Nat → Bool) (hm : ∀ w, digit m w = if M w then 255 else 0)
    (hd : m &&& (m <<< (8 * S)) = 0) : digit (dsw x m (8 * S)) z = digit x (swT M S z) := by
  apply byte_ext _ _ (digit_lt _ _) (digit_lt _ _)
  intro t ht
  rw [← testBit_digit8 _ _ _ ht, ← testBit_digit8 _ _ _ ht, testBit_dsw _ _ _ _ hd]
  have hb : ∀ w, m.testBit (8 * w + t) = M w := fun w => by
    rw [testBit_digit8 _ _ _ ht, hm w, testBit_byte_mask _ _ ht]
  rw [hb z]
  unfold swT
  by_cases h1 : M z = true
  · simp only [h1, if_true]; congr 1; omega
  · simp only [h1]
    by_cases hs : S ≤ z
    · have e : 8 * z + t - 8 * S = 8 * (z - S) + t := by omega
      rw [e, hb]
      by_cases h2 : M (z - S) = true
      · simp [h2, hs, show 8 * S ≤ 8 * z + t by omega]
      · simp [h2]
    · have hs' : ¬ 8 * S ≤ 8 * z + t := by omega
      simp [hs, hs']

/-- Fields `z` whose 512-block offset has index bit `i` set and bit `j` clear. -/
def swP (i j z : Nat) : Bool := z % 512 / 2 ^ i % 2 == 1 && z % 512 / 2 ^ j % 2 == 0

/-- `0xFF` on the fields `z < n` with `swP i j z`, by geometric series (cheap for the kernel). -/
def swMask (i j n : Nat) : Nat :=
  (256 ^ 2 ^ i - 1) * 256 ^ 2 ^ i * ((256 ^ 2 ^ j - 1) / (256 ^ 2 ^ (i + 1) - 1)) *
    ((256 ^ n - 1) / (256 ^ 2 ^ (j + 1) - 1))

theorem digit_swMask (i j m z : Nat)
    (h : swMask i j (512 * m) = pack (tab (fun z => if swP i j z then 255 else 0) 512) * repK 512 m) :
    digit (swMask i j (512 * m)) z = if (decide (z < 512 * m) && swP i j z) then 255 else 0 := by
  rw [h, ← pack_tab_rep, digit_pack _ (tab_bounded _ _ _ (fun _ _ => by split <;> decide))]
  by_cases hz : z < 512 * m
  · rw [tab_getD _ _ _ hz]
    have e : swP i j (z % 512) = swP i j z := by unfold swP; rw [Nat.mod_mod]
    simp [hz, e]
  · have hl : (tab (fun l => (fun z => if swP i j z then 255 else 0) (l % 512)) (512 * m)).length ≤ z := by
      rw [tab_length]; omega
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none hl]
    simp [hz]

/-- The swap predicate on `n` fields. -/
def MK (n i j z : Nat) : Bool := decide (z < n) && swP i j z

/-- Stored position of a code under the 8-symbol layout (three newest digits rotated). -/
def pos8 (z : Nat) : Nat := 512 * (z / 512) + 64 * (z % 8) + z / 8 % 64

/-- The six delta swaps that rotate the nine low index bits of every field by three. -/
def trans8 (n C : Nat) : Nat :=
  dsw (dsw (dsw (dsw (dsw (dsw C (swMask 0 3 n) (8 * 7)) (swMask 3 6 n) (8 * 56)) (swMask 1 4 n) (8 * 14))
    (swMask 4 7 n) (8 * 112)) (swMask 2 5 n) (8 * 28)) (swMask 5 8 n) (8 * 224)

theorem swT_blk03 (m h r : Nat) (hr : r < 512) (hh : h < m) :
    swT (MK (512 * m) 0 3) 7 (512 * h + r) = 512 * h + swT (MK 512 0 3) 7 r := by
  unfold swT MK swP
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, Nat.reducePow]
  split <;> split <;> (try split) <;> (try split) <;> omega
theorem swT_blk36 (m h r : Nat) (hr : r < 512) (hh : h < m) :
    swT (MK (512 * m) 3 6) 56 (512 * h + r) = 512 * h + swT (MK 512 3 6) 56 r := by
  unfold swT MK swP
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, Nat.reducePow]
  split <;> split <;> (try split) <;> (try split) <;> omega
theorem swT_blk14 (m h r : Nat) (hr : r < 512) (hh : h < m) :
    swT (MK (512 * m) 1 4) 14 (512 * h + r) = 512 * h + swT (MK 512 1 4) 14 r := by
  unfold swT MK swP
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, Nat.reducePow]
  split <;> split <;> (try split) <;> (try split) <;> omega
theorem swT_blk47 (m h r : Nat) (hr : r < 512) (hh : h < m) :
    swT (MK (512 * m) 4 7) 112 (512 * h + r) = 512 * h + swT (MK 512 4 7) 112 r := by
  unfold swT MK swP
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, Nat.reducePow]
  split <;> split <;> (try split) <;> (try split) <;> omega
theorem swT_blk25 (m h r : Nat) (hr : r < 512) (hh : h < m) :
    swT (MK (512 * m) 2 5) 28 (512 * h + r) = 512 * h + swT (MK 512 2 5) 28 r := by
  unfold swT MK swP
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, Nat.reducePow]
  split <;> split <;> (try split) <;> (try split) <;> omega
theorem swT_blk58 (m h r : Nat) (hr : r < 512) (hh : h < m) :
    swT (MK (512 * m) 5 8) 224 (512 * h + r) = 512 * h + swT (MK 512 5 8) 224 r := by
  unfold swT MK swP
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, Nat.reducePow]
  split <;> split <;> (try split) <;> (try split) <;> omega

/-- Inside one 512-block: each swap stays in the block, and the six undo the rotation. -/
def comp512ok : Bool :=
  allBelowR 512 fun r =>
    let p := 64 * (r % 8) + r / 8 % 64
    let z6 := swT (MK 512 5 8) 224 p
    let z5 := swT (MK 512 2 5) 28 z6
    let z4 := swT (MK 512 4 7) 112 z5
    let z3 := swT (MK 512 1 4) 14 z4
    let z2 := swT (MK 512 3 6) 56 z3
    let z1 := swT (MK 512 0 3) 7 z2
    p < 512 && z6 < 512 && z5 < 512 && z4 < 512 && z3 < 512 && z2 < 512 && z1 == r
theorem comp512ok_eq : comp512ok = true := by decide +kernel

theorem digit_trans8 (m C y : Nat) (hy : y < 512 * m)
    (e1 : swMask 0 3 (512 * m) = pack (tab (fun z => if swP 0 3 z then 255 else 0) 512) * repK 512 m)
    (e2 : swMask 3 6 (512 * m) = pack (tab (fun z => if swP 3 6 z then 255 else 0) 512) * repK 512 m)
    (e3 : swMask 1 4 (512 * m) = pack (tab (fun z => if swP 1 4 z then 255 else 0) 512) * repK 512 m)
    (e4 : swMask 4 7 (512 * m) = pack (tab (fun z => if swP 4 7 z then 255 else 0) 512) * repK 512 m)
    (e5 : swMask 2 5 (512 * m) = pack (tab (fun z => if swP 2 5 z then 255 else 0) 512) * repK 512 m)
    (e6 : swMask 5 8 (512 * m) = pack (tab (fun z => if swP 5 8 z then 255 else 0) 512) * repK 512 m)
    (d1 : swMask 0 3 (512 * m) &&& (swMask 0 3 (512 * m) <<< (8 * 7)) = 0)
    (d2 : swMask 3 6 (512 * m) &&& (swMask 3 6 (512 * m) <<< (8 * 56)) = 0)
    (d3 : swMask 1 4 (512 * m) &&& (swMask 1 4 (512 * m) <<< (8 * 14)) = 0)
    (d4 : swMask 4 7 (512 * m) &&& (swMask 4 7 (512 * m) <<< (8 * 112)) = 0)
    (d5 : swMask 2 5 (512 * m) &&& (swMask 2 5 (512 * m) <<< (8 * 28)) = 0)
    (d6 : swMask 5 8 (512 * m) &&& (swMask 5 8 (512 * m) <<< (8 * 224)) = 0) :
    digit (trans8 (512 * m) C) (pos8 y) = digit C y := by
  unfold trans8
  rw [digit_dsw _ _ _ _ (MK (512 * m) 5 8) (fun w => digit_swMask 5 8 m w e6) d6,
    digit_dsw _ _ _ _ (MK (512 * m) 2 5) (fun w => digit_swMask 2 5 m w e5) d5,
    digit_dsw _ _ _ _ (MK (512 * m) 4 7) (fun w => digit_swMask 4 7 m w e4) d4,
    digit_dsw _ _ _ _ (MK (512 * m) 1 4) (fun w => digit_swMask 1 4 m w e3) d3,
    digit_dsw _ _ _ _ (MK (512 * m) 3 6) (fun w => digit_swMask 3 6 m w e2) d2,
    digit_dsw _ _ _ _ (MK (512 * m) 0 3) (fun w => digit_swMask 0 3 m w e1) d1]
  have hc := allBelowR_spec _ _ comp512ok_eq (y % 512) (Nat.mod_lt _ (by decide))
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hc
  obtain ⟨⟨⟨⟨⟨⟨hp, h6⟩, h5⟩, h4⟩, h3⟩, h2⟩, h1⟩ := hc
  have hh : y / 512 < m := by omega
  have hpos : pos8 y = 512 * (y / 512) + (64 * (y % 512 % 8) + y % 512 / 8 % 64) := by unfold pos8; omega
  rw [hpos, swT_blk58 m _ _ hp hh, swT_blk25 m _ _ h6 hh, swT_blk47 m _ _ h5 hh, swT_blk14 m _ _ h4 hh,
    swT_blk36 m _ _ h3 hh, swT_blk03 m _ _ h2 hh, h1]
  congr 1; omega

end Snake9.WindowAutomaton
