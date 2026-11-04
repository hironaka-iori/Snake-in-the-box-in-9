import ReplayData161_0000
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

namespace Snake9.ReplayFull161
open Snake9.Lrat144 (andB)
open Snake9.LratFast144
theorem ok4 : check start4 proof4 = true := by
  decide +kernel
#print axioms ok4
theorem ok5 : check start5 proof5 = true := by
  decide +kernel
#print axioms ok5
theorem ok6 : check start6 proof6 = true := by
  decide +kernel
#print axioms ok6
theorem ok7 : check start7 proof7 = true := by
  decide +kernel
#print axioms ok7
end Snake9.ReplayFull161
