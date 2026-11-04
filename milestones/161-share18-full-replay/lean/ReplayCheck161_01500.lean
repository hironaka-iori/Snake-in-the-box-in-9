import ReplayData161_0046
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

namespace Snake9.ReplayFull161
open Snake9.Lrat144 (andB)
open Snake9.LratFast144
theorem ok1500 : check start1500 proof1500 = true := by
  decide +kernel
#print axioms ok1500
theorem ok1501 : check start1501 proof1501 = true := by
  decide +kernel
#print axioms ok1501
theorem ok1502 : check start1502 proof1502 = true := by
  decide +kernel
#print axioms ok1502
theorem ok1503 : andB (check start1503 proof1503) (cpOk (replay start1503 proof1503) start1504) = true := by
  decide +kernel
#print axioms ok1503
end Snake9.ReplayFull161
