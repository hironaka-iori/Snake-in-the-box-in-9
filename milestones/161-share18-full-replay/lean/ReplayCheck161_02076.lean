import ReplayData161_0064
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

namespace Snake9.ReplayFull161
open Snake9.Lrat144 (andB)
open Snake9.LratFast144
theorem ok2076 : check start2076 proof2076 = true := by
  decide +kernel
#print axioms ok2076
theorem ok2077 : check start2077 proof2077 = true := by
  decide +kernel
#print axioms ok2077
theorem ok2078 : check start2078 proof2078 = true := by
  decide +kernel
#print axioms ok2078
theorem ok2079 : andB (check start2079 proof2079) (cpOk (replay start2079 proof2079) start2080) = true := by
  decide +kernel
#print axioms ok2079
end Snake9.ReplayFull161
