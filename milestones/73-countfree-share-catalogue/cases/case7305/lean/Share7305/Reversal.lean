import Share7305.Geometry
namespace Snake9.LocalWindow.ShareWindow7305
set_option maxHeartbeats 1000000
theorem share_bound_rev {m : Nat} (p : Snake m) (r a b c d : Nat)
    (hn : [a,b,c,d].Nodup) (h9 : ∀ x ∈ [a,b,c,d], x < 9)
    (hr : r + 6 ≤ m)
    (hd : ∀ j, j < 6 → dir p (r+j) = ([a,b,d,c,b,a] : List Nat).getD j 0) :
    12 ≤ ((List.range 5).map fun i => coreShare 12 p (r+i+1)).sum := by
  have result := share_bound (revSnake p) (m-r-6) a b c d hn h9
    (by omega)
    (by
      intro j hj
      rw [dir_rev p (by omega), show m - (m-r-6+j) - 1 = r + (5-j) by omega,
        hd (5-j) (by omega)]
      interval_cases j <;> rfl)
  have hs := coreShare_window_rev 12 p r 5 (by omega)
  rw [show m-r-5-1 = m-r-6 by omega] at hs
  rw [hs] at result
  exact result
#print axioms share_bound_rev
end Snake9.LocalWindow.ShareWindow7305
