import ReplayData161_0055
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

namespace Snake9.ReplayFull161
open Snake9.Lrat144 (andB)
open Snake9.LratFast144
theorem ok1788 : check start1788 proof1788 = true := by
  decide +kernel
#print axioms ok1788
theorem ok1789 : check start1789 proof1789 = true := by
  decide +kernel
#print axioms ok1789
theorem ok1790 : check start1790 proof1790 = true := by
  decide +kernel
#print axioms ok1790
theorem ok1791 : andB (check start1791 proof1791) (cpOk (replay start1791 proof1791) start1792) = true := by
  decide +kernel
#print axioms ok1791
end Snake9.ReplayFull161
