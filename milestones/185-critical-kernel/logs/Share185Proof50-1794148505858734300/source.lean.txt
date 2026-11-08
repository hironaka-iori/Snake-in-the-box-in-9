import Share185Proof49
namespace Snake9.LocalWindow.Tags185
open Snake9.LocalWindow.Tags
open Snake9.LocalWindow
variable {S E : Nat → Bool} {M : MT} {X : MS} {Mr : Nat} {cs : List Ctr} {tots : List Tot}
variable {w : List Nat} {cens : List Centre}
theorem sound_shareCap {i cap : Nat} {cl : List Nat} (h : ckShareCap M X tots cap i cl = true)
    (ht : tots.all (totOK M X w cens) = true) (hs : shareSum Mr S cens ≤ cap) :
    clauseTrue (tauS S E M X Mr cs tots) (cl.map decodeLit) = true := by
  match cl, h with
  | [x], h =>
    simp only [ckShareCap, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨hx, hk⟩, h⟩ := h
    split at h
    · rename_i lo hi c ho
      simp only [decide_eq_true_eq] at h
      apply clause_intro; intro hf
      have fx := hf x (by simp)
      rw [lit_neg hx, Bool.not_eq_false', tInfo_sem ho, decide_eq_true_eq] at fx
      have h1 := bc_total (S := S) (E := E) (M := M) (X := X) (Mr := Mr) (tots := tots) i lo hi
      have h2 := cap_total (S := S) (E := E) (Mr := Mr) (totOK_getD ht i) hk
      omega
    · simp at h


end Snake9.LocalWindow.Tags185
