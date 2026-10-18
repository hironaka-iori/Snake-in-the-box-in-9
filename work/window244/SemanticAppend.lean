import LocalWindowTags
namespace Snake9.LocalWindow.Tags
set_option Elab.async false
theorem ckAll_append_true (M : MT) (cs : List Ctr) (w : List Nat)
    (ts : List Tag) (rs : List (List Nat)) (us : List Tag) (vs : List (List Nat))
    (hlen : ts.length = rs.length)
    (ha : ckAll M cs w ts rs = true) (hb : ckAll M cs w us vs = true) :
    ckAll M cs w (ts ++ us) (rs ++ vs) = true := by
  induction ts generalizing rs with
  | nil =>
    cases rs with
    | nil => exact hb
    | cons r rs => simp at hlen
  | cons t ts ih =>
    cases rs with
    | nil => simp at hlen
    | cons r rs =>
      have hlen' : ts.length = rs.length := Nat.succ.inj hlen
      change (ckClause M cs w t r && ckAll M cs w ts rs) = true at ha
      change (ckClause M cs w t r && ckAll M cs w (ts ++ us) (rs ++ vs)) = true
      rw [Bool.and_eq_true] at ha ⊢
      exact ⟨ha.1, ih rs hlen' ha.2⟩
end Snake9.LocalWindow.Tags
