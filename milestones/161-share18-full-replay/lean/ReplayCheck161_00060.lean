import ReplayData161_0001
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

namespace Snake9.ReplayFull161
open Snake9.Lrat144 (andB)
open Snake9.LratFast144
theorem ok60 : check start60 proof60 = true := by
  decide +kernel
#print axioms ok60
theorem ok61 : check start61 proof61 = true := by
  decide +kernel
#print axioms ok61
theorem ok62 : check start62 proof62 = true := by
  decide +kernel
#print axioms ok62
theorem ok63 : andB (check start63 proof63) (cpOk (replay start63 proof63) start64) = true := by
  decide +kernel
#print axioms ok63
end Snake9.ReplayFull161
