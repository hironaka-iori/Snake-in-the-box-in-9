import PrefixChecker100

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace Snake9.Joint103

theorem prefix_interval (depth pref digit code : Nat)
    (hd : depth < 6) (hj : digit < 6)
    (hlo : (6*pref+digit)*6^depth ≤ code)
    (hhi : code < (6*pref+digit+1)*6^depth) :
    (pref*6^(depth+1) ≤ code ∧ code < (pref+1)*6^(depth+1)) ∧
    code%6^(depth+1) = digit*6^depth+code%6^depth := by
  interval_cases depth <;> norm_num at * <;> omega

theorem source_residue (depth digit code : Nat)
    (hd0 : 0 < depth) (hd : depth < 6)
    (hrem : code%6^(depth+1) = digit*6^depth+code%6^depth) :
    (code%6^(depth+1))/6 = digit*6^(depth-1)+(code%6^depth)/6 ∧
    (code%6^depth)/6 < 6^(depth-1) := by
  interval_cases depth <;> norm_num at * <;> omega

theorem target_delay (code : Nat) :
    (code%46656)%7776 = code%7776 := by omega

#print axioms prefix_interval
#print axioms source_residue
#print axioms target_delay
end Snake9.Joint103
