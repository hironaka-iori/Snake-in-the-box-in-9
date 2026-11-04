import ReplayData161_0009
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

namespace Snake9.ReplayFull161
open Snake9.Lrat144 (andB)
open Snake9.LratFast144
theorem ok316 : check start316 proof316 = true := by
  decide +kernel
#print axioms ok316
theorem ok317 : check start317 proof317 = true := by
  decide +kernel
#print axioms ok317
theorem ok318 : check start318 proof318 = true := by
  decide +kernel
#print axioms ok318
theorem ok319 : andB (check start319 proof319) (cpOk (replay start319 proof319) start320) = true := by
  decide +kernel
#print axioms ok319
end Snake9.ReplayFull161
