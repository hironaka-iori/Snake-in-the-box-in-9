import Share186.ClauseAppend
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Snake9.LocalWindow.ShareWindow185
open Snake9.LocalWindow.Tags Snake9.LocalWindow.Tags185
theorem ckAllS_of_split (M : MT) (X : MS) (r : Nat) (cs : List Ctr)
    (ts : List Tot) (w : List Nat) (cap k : Nat)
    (a : List TagS) (b : List (List Nat))
    (hlen : (a.take k).length = (b.take k).length)
    (hl : ckAllS M X r cs ts w cap (a.take k) (b.take k) = true)
    (hr : ckAllS M X r cs ts w cap (a.drop k) (b.drop k) = true) :
    ckAllS M X r cs ts w cap a b = true := by
  have h := ckAllS_append_true M X r cs ts w cap
    (a.take k) (a.drop k) (b.take k) (b.drop k) hlen hl hr
  simpa only [List.take_append_drop] using h
#print axioms ckAllS_of_split
end Snake9.LocalWindow.ShareWindow185
