import LocalWindowTagsShare
namespace Snake9.LocalWindow.Tags
theorem ckAllS_append_true (M : MT) (X : MS) (Mr : Nat) (cs : List Ctr)
    (tots : List Tot) (w : List Nat) (cap : Nat)
    {t1 t2 : List TagS} {r1 r2 : List (List Nat)}
    (h1 : ckAllS M X Mr cs tots w cap t1 r1 = true)
    (h2 : ckAllS M X Mr cs tots w cap t2 r2 = true) :
    ckAllS M X Mr cs tots w cap (t1++t2) (r1++r2) = true := by
  induction t1 generalizing r1 with
  | nil =>
    cases r1 with
    | nil => exact h2
    | cons r rs => simp [ckAllS] at h1
  | cons t ts ih =>
    cases r1 with
    | nil => simp [ckAllS] at h1
    | cons r rs =>
      simp only [ckAllS, Bool.and_eq_true] at h1
      simp only [List.cons_append, ckAllS, Bool.and_eq_true]
      exact ⟨h1.1, ih h1.2⟩
end Snake9.LocalWindow.Tags
