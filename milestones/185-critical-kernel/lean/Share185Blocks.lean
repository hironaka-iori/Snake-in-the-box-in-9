import Share185Basic
namespace Snake9.LocalWindow.Tags185
open Snake9.LocalWindow.Tags
open Snake9.LocalWindow
variable {S E : Nat → Bool} {M : MT} {X : MS} {Mr : Nat} {cs : List Ctr} {tots : List Tot}
variable {w : List Nat} {cens : List Centre}
/-! ### Blocks -/

theorem blk_split (l : List Nat) {lo mid hi : Nat} (h1 : lo ≤ mid) (h2 : mid ≤ hi) :
    blk l lo hi = blk l lo mid ++ blk l mid hi := by
  unfold blk
  rw [show hi - lo = (mid - lo) + (hi - mid) by omega, List.take_add, List.drop_drop,
    show lo + (mid - lo) = mid by omega]

theorem countP_blk_split (f : Nat → Bool) (l : List Nat) {lo mid hi : Nat} (h1 : lo ≤ mid)
    (h2 : mid ≤ hi) :
    (blk l lo hi).countP f = (blk l lo mid).countP f + (blk l mid hi).countP f := by
  rw [blk_split l h1 h2, List.countP_append]

theorem countP_blk_le (f : Nat → Bool) (l : List Nat) (lo hi : Nat) :
    (blk l lo hi).countP f ≤ hi - lo :=
  Nat.le_trans (List.countP_le_length) (List.length_take_le _ _)

theorem countP_blk_total (f : Nat → Bool) (l : List Nat) (lo hi : Nat) :
    (blk l lo hi).countP f ≤ l.countP f :=
  ((List.take_sublist _ _).trans (List.drop_sublist _ _)).countP_le

theorem totOK_getD {w : List Nat} {cens : List Centre} (h : tots.all (totOK M X w cens) = true)
    (i : Nat) : totOK M X w cens (tots.getD i dfltTot) = true := by
  rw [List.getD_eq_getElem?_getD]
  cases hc : tots[i]? with
  | none => simp [totOK, dfltTot, capL]
  | some t => exact List.all_eq_true.1 h t (List.mem_of_getElem? hc)

theorem totOK_lits {w : List Nat} {cens : List Centre} {t : Tot} (h : totOK M X w cens t = true) :
    ∀ l ∈ t.lits, baseOKS M X l = true := by
  unfold totOK at h
  rw [Bool.and_eq_true, List.all_eq_true] at h
  exact h.1

theorem litInfo_sem {w : List Nat} {cens : List Centre} (ht : tots.all (totOK M X w cens) = true)
    {i a pos lo hi c : Nat} (h : litInfo M X tots i a pos = some (lo, hi, c)) :
    lv (tauS S E M X Mr cs tots) a = decide (c ≤ bc S E M X Mr tots i lo hi) := by
  unfold litInfo at h
  split at h
  · rename_i r hr
    simp only [Option.some.injEq] at h
    subst h
    exact tInfo_sem hr
  · split at h
    · rename_i hc
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      obtain ⟨ha, hpos⟩ := hc
      have hmem : a ∈ (tots.getD i dfltTot).lits := by rw [ha]; exact getD_mem hpos
      rw [lv_base_ok (totOK_lits (totOK_getD ht i) a hmem)]
      unfold bc blk
      rw [show pos + 1 - pos = 1 by omega, List.drop_eq_getElem_cons hpos]
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hpos] at ha
      simp only [Option.getD_some] at ha
      rw [← ha]
      cases hb : lv (baseS S E M X Mr) a <;> simp [hb]
    · simp at h


end Snake9.LocalWindow.Tags185
