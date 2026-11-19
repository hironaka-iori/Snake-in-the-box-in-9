/-! Bit facts for the facet split Q9 = Q8 x Q1 along coordinate i, all checked by `decide`. -/
set_option maxRecDepth 200000
namespace Dim8Lift

def proj (i w : Nat) : Nat := w % 2 ^ i + (w / 2 ^ (i + 1)) * 2 ^ i
def emb (i u : Nat) (b : Bool) : Nat := u % 2 ^ i + (if b then 2 ^ i else 0) + (u / 2 ^ i) * 2 ^ (i + 1)
def sh (i a : Nat) : Nat := if a < i then a else a + 1

theorem bits_proj_flip_F : ∀ i : Fin 9, ∀ w : Fin 512, ∀ a : Fin 8,
    proj i.val (w.val ^^^ 2 ^ (sh i.val a.val)) = proj i.val w.val ^^^ 2 ^ a.val ∧
    (w.val ^^^ 2 ^ (sh i.val a.val)).testBit i.val = w.val.testBit i.val := by decide

theorem bits_emb_proj_F : ∀ i : Fin 9, ∀ w : Fin 512, emb i.val (proj i.val w.val) (w.val.testBit i.val) = w.val := by
  decide

theorem bits_proj_lt_F : ∀ i : Fin 9, ∀ w : Fin 512, proj i.val w.val < 256 := by decide

theorem bits_flip_F : ∀ i : Fin 9, ∀ w : Fin 512, ∀ k : Fin 9,
    ((w.val ^^^ 2 ^ k.val).testBit i.val != w.val.testBit i.val) = (i.val == k.val) := by decide

theorem bits_q8_lt_F : ∀ u : Fin 256, ∀ a : Fin 8, u.val ^^^ 2 ^ a.val < 256 := by decide

theorem bits_q8_ne_F : ∀ u : Fin 256, ∀ a : Fin 8, ∀ b : Fin 8, a.val ≠ b.val → u.val ^^^ 2 ^ a.val ≠ u.val ^^^ 2 ^ b.val := by
  decide

theorem bits_q8_ne0_F : ∀ u : Fin 256, ∀ a : Fin 8, u.val ^^^ 2 ^ a.val ≠ u.val := by decide

theorem bits_q9_lt_F : ∀ w : Fin 512, ∀ k : Fin 9, w.val ^^^ 2 ^ k.val < 512 := by decide

theorem bits_q9_ne0_F : ∀ w : Fin 512, ∀ k : Fin 9, w.val ^^^ 2 ^ k.val ≠ w.val := by decide

theorem bits_xor_xor_F : ∀ u : Fin 256, ∀ a : Fin 8, (u.val ^^^ 2 ^ a.val) ^^^ 2 ^ a.val = u.val := by decide

theorem proj_flip {i w a : Nat} (hi : i < 9) (hw : w < 512) (ha : a < 8) :
    proj i (w ^^^ 2 ^ (sh i a)) = proj i w ^^^ 2 ^ a :=
  (bits_proj_flip_F ⟨i, hi⟩ ⟨w, hw⟩ ⟨a, ha⟩).1
theorem bit_flip_sh {i w a : Nat} (hi : i < 9) (hw : w < 512) (ha : a < 8) :
    (w ^^^ 2 ^ (sh i a)).testBit i = w.testBit i :=
  (bits_proj_flip_F ⟨i, hi⟩ ⟨w, hw⟩ ⟨a, ha⟩).2
theorem emb_proj {i w : Nat} (hi : i < 9) (hw : w < 512) : emb i (proj i w) (w.testBit i) = w :=
  bits_emb_proj_F ⟨i, hi⟩ ⟨w, hw⟩
theorem proj_lt {i w : Nat} (hi : i < 9) (hw : w < 512) : proj i w < 256 := bits_proj_lt_F ⟨i, hi⟩ ⟨w, hw⟩
theorem bit_flip {i w k : Nat} (hi : i < 9) (hw : w < 512) (hk : k < 9) :
    ((w ^^^ 2 ^ k).testBit i != w.testBit i) = (i == k) := bits_flip_F ⟨i, hi⟩ ⟨w, hw⟩ ⟨k, hk⟩
theorem q8_lt {u a : Nat} (hu : u < 256) (ha : a < 8) : u ^^^ 2 ^ a < 256 := bits_q8_lt_F ⟨u, hu⟩ ⟨a, ha⟩
theorem q8_ne {u a b : Nat} (hu : u < 256) (ha : a < 8) (hb : b < 8) (h : a ≠ b) :
    u ^^^ 2 ^ a ≠ u ^^^ 2 ^ b := bits_q8_ne_F ⟨u, hu⟩ ⟨a, ha⟩ ⟨b, hb⟩ h
theorem q8_ne0 {u a : Nat} (hu : u < 256) (ha : a < 8) : u ^^^ 2 ^ a ≠ u := bits_q8_ne0_F ⟨u, hu⟩ ⟨a, ha⟩
theorem q9_lt {w k : Nat} (hw : w < 512) (hk : k < 9) : w ^^^ 2 ^ k < 512 := bits_q9_lt_F ⟨w, hw⟩ ⟨k, hk⟩
theorem q9_ne0 {w k : Nat} (hw : w < 512) (hk : k < 9) : w ^^^ 2 ^ k ≠ w := bits_q9_ne0_F ⟨w, hw⟩ ⟨k, hk⟩
theorem q8_xx {u a : Nat} (hu : u < 256) (ha : a < 8) : (u ^^^ 2 ^ a) ^^^ 2 ^ a = u := bits_xor_xor_F ⟨u, hu⟩ ⟨a, ha⟩

/-- A flip of coordinate k ≠ i is the flip `sh i a` of some a < 8. -/
theorem sh_cover {i k : Nat} (hi : i < 9) (hk : k < 9) (hne : k ≠ i) : ∃ a, a < 8 ∧ sh i a = k := by
  by_cases h : k < i
  · exact ⟨k, by omega, by simp [sh, h]⟩
  · exact ⟨k - 1, by omega, by simp [sh]; split <;> omega⟩

end Dim8Lift
