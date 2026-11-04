import ReplayData161_0003
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

namespace Snake9.ReplayFull161
open Snake9.Lrat144 (andB)
open Snake9.LratFast144
theorem ok124 : check start124 proof124 = true := by
  decide +kernel
#print axioms ok124
theorem ok125 : check start125 proof125 = true := by
  decide +kernel
#print axioms ok125
theorem ok126 : check start126 proof126 = true := by
  decide +kernel
#print axioms ok126
theorem ok127 : andB (check start127 proof127) (cpOk (replay start127 proof127) start128) = true := by
  decide +kernel
#print axioms ok127
end Snake9.ReplayFull161
