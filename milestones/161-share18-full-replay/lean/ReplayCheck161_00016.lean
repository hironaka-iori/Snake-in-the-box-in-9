import ReplayData161_0000
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

namespace Snake9.ReplayFull161
open Snake9.Lrat144 (andB)
open Snake9.LratFast144
theorem ok16 : check start16 proof16 = true := by
  decide +kernel
#print axioms ok16
theorem ok17 : check start17 proof17 = true := by
  decide +kernel
#print axioms ok17
theorem ok18 : check start18 proof18 = true := by
  decide +kernel
#print axioms ok18
theorem ok19 : check start19 proof19 = true := by
  decide +kernel
#print axioms ok19
end Snake9.ReplayFull161
