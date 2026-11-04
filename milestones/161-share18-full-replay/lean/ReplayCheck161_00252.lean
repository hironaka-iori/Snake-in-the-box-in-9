import ReplayData161_0007
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

namespace Snake9.ReplayFull161
open Snake9.Lrat144 (andB)
open Snake9.LratFast144
theorem ok252 : check start252 proof252 = true := by
  decide +kernel
#print axioms ok252
theorem ok253 : check start253 proof253 = true := by
  decide +kernel
#print axioms ok253
theorem ok254 : check start254 proof254 = true := by
  decide +kernel
#print axioms ok254
theorem ok255 : andB (check start255 proof255) (cpOk (replay start255 proof255) start256) = true := by
  decide +kernel
#print axioms ok255
end Snake9.ReplayFull161
