import ReplayData161_0011
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

namespace Snake9.ReplayFull161
open Snake9.Lrat144 (andB)
open Snake9.LratFast144
theorem ok360 : check start360 proof360 = true := by
  decide +kernel
#print axioms ok360
theorem ok361 : check start361 proof361 = true := by
  decide +kernel
#print axioms ok361
theorem ok362 : check start362 proof362 = true := by
  decide +kernel
#print axioms ok362
theorem ok363 : check start363 proof363 = true := by
  decide +kernel
#print axioms ok363
end Snake9.ReplayFull161
