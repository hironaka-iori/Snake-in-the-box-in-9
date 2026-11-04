import ReplayData161_0071
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

namespace Snake9.ReplayFull161
open Snake9.Lrat144 (andB)
open Snake9.LratFast144
theorem ok2300 : check start2300 proof2300 = true := by
  decide +kernel
#print axioms ok2300
theorem ok2301 : check start2301 proof2301 = true := by
  decide +kernel
#print axioms ok2301
theorem ok2302 : check start2302 proof2302 = true := by
  decide +kernel
#print axioms ok2302
theorem ok2303 : andB (check start2303 proof2303) (cpOk (replay start2303 proof2303) start2304) = true := by
  decide +kernel
#print axioms ok2303
end Snake9.ReplayFull161
