import Std

namespace LossTradeoff177

theorem max_weight_transfer (s a f g c h : Nat) (hf : f ≤ g+1) :
    max s (a+max f c)+h ≤ max s (a+max g c)+h+1 := by omega

theorem edge_transfer (w w' pu pv mean : Int)
    (h : mean≤9*w+pu-pv) (hw : w≤w'+1) :
    mean-9≤9*w'+pu-pv := by omega

theorem uniform14_comparison (m W G L : Nat) (hm : 8≤m)
    (hb : G+840*(m+1)+L≤221136) (hp : W+2880≤5*G)
    (hw : 4444*(m-8)≤9*W+5384) :
    42244*m+45*L≤9928336 := by omega

theorem uniform14_upper234 (m W G L : Nat) (hm : 8≤m)
    (hb : G+840*(m+1)+L≤221136) (hp : W+2880≤5*G)
    (hw : 4444*(m-8)≤9*W+5384) (hl : 23≤L) : m≤234 := by
  have := uniform14_comparison m W G L hm hb hp hw
  omega

theorem single14_comparison (m W G L : Nat) (hm : 8≤m)
    (hb : G+840*(m+1)+L≤221136) (hp : W+2880≤5*G)
    (hw : 4445*(m-8)≤9*W+5374) :
    42245*m+45*L≤9928334 := by omega

theorem single14_upper234 (m W G L : Nat) (hm : 8≤m)
    (hb : G+840*(m+1)+L≤221136) (hp : W+2880≤5*G)
    (hw : 4445*(m-8)≤9*W+5374) (hl : 17≤L) : m≤234 := by
  have := single14_comparison m W G L hm hb hp hw
  omega

theorem loss_cutoffs_at235 (L : Nat) :
    (42244*235+45*L≤9928336 ↔ L≤22) ∧
    (42245*235+45*L≤9928334 ↔ L≤16) := by omega

theorem retuned14_range_criterion (m W G L R : Nat) (hm : 8≤m)
    (hb : G+840*(m+1)+L≤221136) (hp : W+2880≤5*G)
    (hw : 4448*(m-8)≤9*W+R) (hr : R+1≤5296+45*L) : m≤234 := by
  omega

#print axioms max_weight_transfer
#print axioms edge_transfer
#print axioms uniform14_comparison
#print axioms uniform14_upper234
#print axioms single14_comparison
#print axioms single14_upper234
#print axioms loss_cutoffs_at235
#print axioms retuned14_range_criterion
end LossTradeoff177
