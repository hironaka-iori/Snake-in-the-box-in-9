import ReplayData161_0065
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

namespace Snake9.ReplayFull161
open Snake9.Lrat144 (andB)
open Snake9.LratFast144
theorem ok2108 : check start2108 proof2108 = true := by
  decide +kernel
#print axioms ok2108
theorem ok2109 : check start2109 proof2109 = true := by
  decide +kernel
#print axioms ok2109
theorem ok2110 : check start2110 proof2110 = true := by
  decide +kernel
#print axioms ok2110
theorem ok2111 : andB (check start2111 proof2111) (cpOk (replay start2111 proof2111) start2112) = true := by
  decide +kernel
#print axioms ok2111
end Snake9.ReplayFull161
