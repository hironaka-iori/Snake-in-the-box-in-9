import ReplayData161_0064
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

namespace Snake9.ReplayFull161
open Snake9.Lrat144 (andB)
open Snake9.LratFast144
theorem ok2048 : check start2048 proof2048 = true := by
  decide +kernel
#print axioms ok2048
theorem ok2049 : check start2049 proof2049 = true := by
  decide +kernel
#print axioms ok2049
theorem ok2050 : check start2050 proof2050 = true := by
  decide +kernel
#print axioms ok2050
theorem ok2051 : check start2051 proof2051 = true := by
  decide +kernel
#print axioms ok2051
end Snake9.ReplayFull161
