import ReplayData161_0066
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

namespace Snake9.ReplayFull161
open Snake9.Lrat144 (andB)
open Snake9.LratFast144
theorem ok2140 : check start2140 proof2140 = true := by
  decide +kernel
#print axioms ok2140
theorem ok2141 : check start2141 proof2141 = true := by
  decide +kernel
#print axioms ok2141
theorem ok2142 : check start2142 proof2142 = true := by
  decide +kernel
#print axioms ok2142
theorem ok2143 : andB (check start2143 proof2143) (cpOk (replay start2143 proof2143) start2144) = true := by
  decide +kernel
#print axioms ok2143
end Snake9.ReplayFull161
