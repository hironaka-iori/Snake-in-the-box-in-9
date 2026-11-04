import ReplayData161_0059
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

namespace Snake9.ReplayFull161
open Snake9.Lrat144 (andB)
open Snake9.LratFast144
theorem ok1916 : check start1916 proof1916 = true := by
  decide +kernel
#print axioms ok1916
theorem ok1917 : check start1917 proof1917 = true := by
  decide +kernel
#print axioms ok1917
theorem ok1918 : check start1918 proof1918 = true := by
  decide +kernel
#print axioms ok1918
theorem ok1919 : andB (check start1919 proof1919) (cpOk (replay start1919 proof1919) start1920) = true := by
  decide +kernel
#print axioms ok1919
end Snake9.ReplayFull161
