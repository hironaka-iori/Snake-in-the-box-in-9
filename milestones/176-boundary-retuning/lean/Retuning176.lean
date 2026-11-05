import Std
namespace Retuning176

theorem one_unit_edge_transfer (w w' pu pv : Int)
    (h : 4462≤9*w+pu-pv) (hw : w≤w'+1) :
    4453≤9*w'+pu-pv := by omega

theorem one_unit_comparison (m W G L : Nat)
    (hb : G+840*(m+1)+L≤221136) (hp : W+2880≤5*G)
    (hw : 4453*(m-8)≤9*W+5411) : m≤234 := by omega

theorem one_unit_exact (m W G L : Nat) (hm : 8≤m)
    (hb : G+840*(m+1)+L≤221136) (hp : W+2880≤5*G)
    (hw : 4453*(m-8)≤9*W+5411) : 42253*m+45*L≤9928435 := by omega

theorem seven_disjoint_occurrences (m s Sigma : Nat)
    (hc : 39*m+2*s≤9192) (hshare : Sigma≤48*s) (hocc : 7*96≤Sigma) :
    m≤234 := by omega

theorem thirty_three_overlapping_occurrences (m s Sigma : Nat)
    (hc : 39*m+2*s≤9192) (hshare : Sigma≤48*s) (hocc : 33*96≤5*Sigma) :
    m≤234 := by omega

theorem floor14_all_means_obstruction (p d R : Nat) (hd : 1≤d)
    (hcycle : 9*p≤4448*d) (hwalk : 9*p≤3858*d+R) :
    227*p≤111600*d+R := by omega

theorem floor14_strict_margin (p d R : Nat)
    (hcycle : 9*p≤4448*d) (hwalk : 9*p≤3858*d+R) :
    9*(227*p)+14*d≤9*(111600*d+R) := by omega

theorem floor15_range_criterion (m W G L R : Nat)
    (hb : G+840*(m+1)+L≤221136) (hp : W+2880≤5*G)
    (hw : 4454*(m-8)≤9*W+R) (hr : R≤6657) : m≤234 := by omega

#print axioms floor14_all_means_obstruction
#print axioms floor14_strict_margin
#print axioms floor15_range_criterion
#print axioms one_unit_edge_transfer
#print axioms one_unit_comparison
#print axioms one_unit_exact
#print axioms seven_disjoint_occurrences
#print axioms thirty_three_overlapping_occurrences
end Retuning176
