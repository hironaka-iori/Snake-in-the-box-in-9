import ReplayData161_0010
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

namespace Snake9.ReplayFull161
open Snake9.Lrat144 (andB)
open Snake9.LratFast144
theorem ok348 : check start348 proof348 = true := by
  decide +kernel
#print axioms ok348
theorem ok349 : check start349 proof349 = true := by
  decide +kernel
#print axioms ok349
theorem ok350 : check start350 proof350 = true := by
  decide +kernel
#print axioms ok350
theorem ok351 : andB (check start351 proof351) (cpOk (replay start351 proof351) start352) = true := by
  decide +kernel
#print axioms ok351
end Snake9.ReplayFull161
