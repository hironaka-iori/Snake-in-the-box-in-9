import ReplayData161_0006
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

namespace Snake9.ReplayFull161
open Snake9.Lrat144 (andB)
open Snake9.LratFast144
theorem ok220 : check start220 proof220 = true := by
  decide +kernel
#print axioms ok220
theorem ok221 : check start221 proof221 = true := by
  decide +kernel
#print axioms ok221
theorem ok222 : check start222 proof222 = true := by
  decide +kernel
#print axioms ok222
theorem ok223 : andB (check start223 proof223) (cpOk (replay start223 proof223) start224) = true := by
  decide +kernel
#print axioms ok223
end Snake9.ReplayFull161
