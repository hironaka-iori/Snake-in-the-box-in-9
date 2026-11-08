import Share185Proof20
namespace Snake9.LocalWindow.Tags185
open Snake9.LocalWindow.Tags
open Snake9.LocalWindow
variable {S E : Nat → Bool} {M : MT} {X : MS} {Mr : Nat} {cs : List Ctr} {tots : List Tot}
variable {w : List Nat} {cens : List Centre}
theorem tInfo_sem {i a lo hi c : Nat} (h : tInfo M X i a = some (lo, hi, c)) :
    lv (tauS S E M X Mr cs tots) a = decide (c ≤ bc S E M X Mr tots i lo hi) := by
  unfold tInfo at h
  split at h
  · rename_i hp
    obtain ⟨h0, _, hn⟩ := posS_parts hp
    split at h
    · rename_i i' lo' hi' c' hX
      split at h
      · rename_i hi'
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl, rfl⟩ := h
        subst hi'
        simp only [lv, h0, if_true]
        unfold tauS; rw [if_neg (by simp [hn]), hX]
      · simp at h
    · simp at h
  · simp at h

/-! ### Blocks -/


end Snake9.LocalWindow.Tags185
