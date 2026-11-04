import ReplayData161_0070
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

namespace Snake9.ReplayFull161
open Snake9.Lrat144 (andB)
open Snake9.LratFast144
theorem ok2268 : check start2268 proof2268 = true := by
  decide +kernel
#print axioms ok2268
theorem ok2269 : check start2269 proof2269 = true := by
  decide +kernel
#print axioms ok2269
theorem ok2270 : check start2270 proof2270 = true := by
  decide +kernel
#print axioms ok2270
theorem ok2271 : andB (check start2271 proof2271) (cpOk (replay start2271 proof2271) start2272) = true := by
  decide +kernel
#print axioms ok2271
end Snake9.ReplayFull161
