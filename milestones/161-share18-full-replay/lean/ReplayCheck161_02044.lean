import ReplayData161_0063
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

namespace Snake9.ReplayFull161
open Snake9.Lrat144 (andB)
open Snake9.LratFast144
theorem ok2044 : check start2044 proof2044 = true := by
  decide +kernel
#print axioms ok2044
theorem ok2045 : check start2045 proof2045 = true := by
  decide +kernel
#print axioms ok2045
theorem ok2046 : check start2046 proof2046 = true := by
  decide +kernel
#print axioms ok2046
theorem ok2047 : andB (check start2047 proof2047) (cpOk (replay start2047 proof2047) start2048) = true := by
  decide +kernel
#print axioms ok2047
end Snake9.ReplayFull161
