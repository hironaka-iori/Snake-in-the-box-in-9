import Share185.DirectData
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Snake9.LocalWindow.ShareWindow185
open Snake9.LocalWindow.Tags Snake9.LocalWindow.Tags185
theorem ckAllS_append_true (M : MT) (X : MS) (r : Nat) (cs : List Ctr)
    (ts : List Tot) (w : List Nat) (k : Nat)
    (a b : List TagS) (c d : List (List Nat)) (hlen : a.length = c.length)
    (ha : ckAllS M X r cs ts w k a c = true)
    (hb : ckAllS M X r cs ts w k b d = true) :
    ckAllS M X r cs ts w k (a ++ b) (c ++ d) = true := by
  induction a generalizing c with
  | nil =>
    cases c with
    | nil => exact hb
    | cons x xs => simp at hlen
  | cons x xs ih =>
    cases c with
    | nil => simp at hlen
    | cons y ys =>
      simp only [List.length_cons,Nat.succ.injEq] at hlen
      simp only [ckAllS,Bool.and_eq_true] at ha
      simp only [List.cons_append,ckAllS,ha.1,ih ys hlen ha.2,Bool.and_self]
#print axioms ckAllS_append_true
end Snake9.LocalWindow.ShareWindow185
