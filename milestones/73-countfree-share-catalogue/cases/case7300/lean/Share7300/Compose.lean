import LocalWindowTagsShare
import Mathlib.Tactic
namespace Snake9.LocalWindow.Tags
set_option maxHeartbeats 0
theorem ckAllS_append_true7300 (M : MT) (X : MS) (Mr : Nat) (cs : List Ctr)
    (tots : List Tot) (w : List Nat) (cap : Nat)
    (ts us : List TagS) (rs ss : List (List Nat))
    (h : ckAllS M X Mr cs tots w cap ts rs = true)
    (k : ckAllS M X Mr cs tots w cap us ss = true) :
    ckAllS M X Mr cs tots w cap (ts ++ us) (rs ++ ss) = true := by
  induction ts generalizing rs with
  | nil =>
    cases rs with
    | nil => simpa using k
    | cons r rs => simp [ckAllS] at h
  | cons t ts ih =>
    cases rs with
    | nil => simp [ckAllS] at h
    | cons r rs =>
      simp only [ckAllS, Bool.and_eq_true] at h
      simp only [List.cons_append, ckAllS, Bool.and_eq_true]
      exact ⟨h.1, ih rs h.2⟩
#print axioms ckAllS_append_true7300
end Snake9.LocalWindow.Tags
