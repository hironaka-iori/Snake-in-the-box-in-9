import ReplayData161_0050
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

namespace Snake9.ReplayFull161
open Snake9.Lrat144 (andB)
open Snake9.LratFast144
theorem ok1600 : check start1600 proof1600 = true := by
  decide +kernel
#print axioms ok1600
theorem ok1601 : check start1601 proof1601 = true := by
  decide +kernel
#print axioms ok1601
theorem ok1602 : check start1602 proof1602 = true := by
  decide +kernel
#print axioms ok1602
theorem ok1603 : check start1603 proof1603 = true := by
  decide +kernel
#print axioms ok1603
end Snake9.ReplayFull161
