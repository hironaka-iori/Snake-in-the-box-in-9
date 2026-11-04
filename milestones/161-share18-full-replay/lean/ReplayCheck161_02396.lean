import ReplayData161_0074
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

namespace Snake9.ReplayFull161
open Snake9.Lrat144 (andB)
open Snake9.LratFast144
theorem ok2396 : check start2396 proof2396 = true := by
  decide +kernel
#print axioms ok2396
theorem ok2397 : check start2397 proof2397 = true := by
  decide +kernel
#print axioms ok2397
theorem ok2398 : check start2398 proof2398 = true := by
  decide +kernel
#print axioms ok2398
theorem ok2399 : andB (check start2399 proof2399) (cpOk (replay start2399 proof2399) start2400) = true := by
  decide +kernel
#print axioms ok2399
end Snake9.ReplayFull161
