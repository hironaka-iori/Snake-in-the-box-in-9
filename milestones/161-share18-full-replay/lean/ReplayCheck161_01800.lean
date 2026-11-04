import ReplayData161_0056
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

namespace Snake9.ReplayFull161
open Snake9.Lrat144 (andB)
open Snake9.LratFast144
theorem ok1800 : check start1800 proof1800 = true := by
  decide +kernel
#print axioms ok1800
theorem ok1801 : check start1801 proof1801 = true := by
  decide +kernel
#print axioms ok1801
theorem ok1802 : check start1802 proof1802 = true := by
  decide +kernel
#print axioms ok1802
theorem ok1803 : check start1803 proof1803 = true := by
  decide +kernel
#print axioms ok1803
end Snake9.ReplayFull161
