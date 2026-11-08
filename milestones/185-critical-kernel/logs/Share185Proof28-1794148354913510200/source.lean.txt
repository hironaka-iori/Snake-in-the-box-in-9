import Share185Proof27
namespace Snake9.LocalWindow.Tags185
open Snake9.LocalWindow.Tags
open Snake9.LocalWindow
variable {S E : Nat → Bool} {M : MT} {X : MS} {Mr : Nat} {cs : List Ctr} {tots : List Tot}
variable {w : List Nat} {cens : List Centre}
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

/-! ### Totalizer kinds -/


end Snake9.LocalWindow.Tags185
