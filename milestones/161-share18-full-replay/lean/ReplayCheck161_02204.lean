import ReplayData161_0068
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

namespace Snake9.ReplayFull161
open Snake9.Lrat144 (andB)
open Snake9.LratFast144
theorem ok2204 : check start2204 proof2204 = true := by
  decide +kernel
#print axioms ok2204
theorem ok2205 : check start2205 proof2205 = true := by
  decide +kernel
#print axioms ok2205
theorem ok2206 : check start2206 proof2206 = true := by
  decide +kernel
#print axioms ok2206
theorem ok2207 : andB (check start2207 proof2207) (cpOk (replay start2207 proof2207) start2208) = true := by
  decide +kernel
#print axioms ok2207
end Snake9.ReplayFull161
