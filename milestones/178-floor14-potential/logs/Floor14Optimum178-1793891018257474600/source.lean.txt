import Std
namespace Floor14Optimum178
theorem fixed_comparison (m W G L : Nat) (hm : 8≤m)
    (hb : G+840*(m+1)+L≤221136) (hp : W+2880≤5*G)
    (hw : 4448*(m-8)≤9*W+5346) :
    42248*m+45*L≤9928330 := by omega

theorem uniform_comparison (m W G L : Nat) (hm : 8≤m)
    (hb : G+840*(m+1)+L≤221136) (hp : W+2880≤5*G)
    (hw : 4448*(m-8)≤9*W+5380) :
    42248*m+45*L≤9928364 := by omega

theorem uniform_upper234 (m W G L : Nat) (hm : 8≤m)
    (hb : G+840*(m+1)+L≤221136) (hp : W+2880≤5*G)
    (hw : 4448*(m-8)≤9*W+5380) (hl : 2≤L) : m≤234 := by
  have := uniform_comparison m W G L hm hb hp hw
  omega

theorem critical_zero_or_one (m W G L : Nat) (hm : 235≤m)
    (hb : G+840*(m+1)+L≤221136) (hp : W+2880≤5*G)
    (hw : 4448*(m-8)≤9*W+5380) : m=235 ∧ (L=0 ∨ L=1) := by
  have := uniform_comparison m W G L (by omega) hb hp hw
  omega


#print axioms fixed_comparison
#print axioms uniform_comparison
#print axioms uniform_upper234
#print axioms critical_zero_or_one
end Floor14Optimum178
