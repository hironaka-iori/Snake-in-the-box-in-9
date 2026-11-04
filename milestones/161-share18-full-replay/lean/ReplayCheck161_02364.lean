import ReplayData161_0073
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

namespace Snake9.ReplayFull161
open Snake9.Lrat144 (andB)
open Snake9.LratFast144
theorem ok2364 : check start2364 proof2364 = true := by
  decide +kernel
#print axioms ok2364
theorem ok2365 : check start2365 proof2365 = true := by
  decide +kernel
#print axioms ok2365
theorem ok2366 : check start2366 proof2366 = true := by
  decide +kernel
#print axioms ok2366
theorem ok2367 : andB (check start2367 proof2367) (cpOk (replay start2367 proof2367) start2368) = true := by
  decide +kernel
#print axioms ok2367
end Snake9.ReplayFull161
