import ReplayData161_0069
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

namespace Snake9.ReplayFull161
open Snake9.Lrat144 (andB)
open Snake9.LratFast144
theorem ok2236 : check start2236 proof2236 = true := by
  decide +kernel
#print axioms ok2236
theorem ok2237 : check start2237 proof2237 = true := by
  decide +kernel
#print axioms ok2237
theorem ok2238 : check start2238 proof2238 = true := by
  decide +kernel
#print axioms ok2238
theorem ok2239 : andB (check start2239 proof2239) (cpOk (replay start2239 proof2239) start2240) = true := by
  decide +kernel
#print axioms ok2239
end Snake9.ReplayFull161
