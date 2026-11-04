import ReplayData161_0072
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

namespace Snake9.ReplayFull161
open Snake9.Lrat144 (andB)
open Snake9.LratFast144
theorem ok2332 : check start2332 proof2332 = true := by
  decide +kernel
#print axioms ok2332
theorem ok2333 : check start2333 proof2333 = true := by
  decide +kernel
#print axioms ok2333
theorem ok2334 : check start2334 proof2334 = true := by
  decide +kernel
#print axioms ok2334
theorem ok2335 : andB (check start2335 proof2335) (cpOk (replay start2335 proof2335) start2336) = true := by
  decide +kernel
#print axioms ok2335
end Snake9.ReplayFull161
