import ReplayData161_0059
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

namespace Snake9.ReplayFull161
open Snake9.Lrat144 (andB)
open Snake9.LratFast144
theorem ok1900 : check start1900 proof1900 = true := by
  decide +kernel
#print axioms ok1900
theorem ok1901 : check start1901 proof1901 = true := by
  decide +kernel
#print axioms ok1901
theorem ok1902 : check start1902 proof1902 = true := by
  decide +kernel
#print axioms ok1902
theorem ok1903 : check start1903 proof1903 = true := by
  decide +kernel
#print axioms ok1903
end Snake9.ReplayFull161
