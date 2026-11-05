import Std
namespace Floor15Optimum176

theorem joint_mean_range_lower_bound (p d R : Nat)
    (hcycle : 9*p≤4454*d) (hwalk : 8*p≤3362*d+R) :
    4964203*(4200*d+p)≤21127*(1098600*d+8*p+R) := by omega

theorem equality_parameters (p d R : Nat)
    (hcycle : 9*p≤4454*d) (hwalk : 8*p≤3362*d+R)
    (he : 4964203*(4200*d+p)=21127*(1098600*d+8*p+R)) :
    9*p=4454*d ∧ 9*R=5374*d := by omega

theorem actual_comparison_arithmetic (m W G L : Nat) (hm : 8≤m)
    (hb : G+840*(m+1)+L≤221136) (hp : W+2880≤5*G)
    (hw : 4454*(m-8)≤9*W+5374) :
    42254*m+45*L≤9928406 ∧ m≤234 := by omega

#print axioms joint_mean_range_lower_bound
#print axioms equality_parameters
#print axioms actual_comparison_arithmetic
end Floor15Optimum176
