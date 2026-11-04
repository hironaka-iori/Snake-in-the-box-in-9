import ReplayData161_0031
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

namespace Snake9.ReplayFull161
open Snake9.Lrat144 (andB)
open Snake9.LratFast144
theorem ok1020 : check start1020 proof1020 = true := by
  decide +kernel
#print axioms ok1020
theorem ok1021 : check start1021 proof1021 = true := by
  decide +kernel
#print axioms ok1021
theorem ok1022 : check start1022 proof1022 = true := by
  decide +kernel
#print axioms ok1022
theorem ok1023 : andB (check start1023 proof1023) (cpOk (replay start1023 proof1023) start1024) = true := by
  decide +kernel
#print axioms ok1023
end Snake9.ReplayFull161
