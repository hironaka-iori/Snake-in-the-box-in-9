import ReplayData161_0067
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

namespace Snake9.ReplayFull161
open Snake9.Lrat144 (andB)
open Snake9.LratFast144
theorem ok2172 : check start2172 proof2172 = true := by
  decide +kernel
#print axioms ok2172
theorem ok2173 : check start2173 proof2173 = true := by
  decide +kernel
#print axioms ok2173
theorem ok2174 : check start2174 proof2174 = true := by
  decide +kernel
#print axioms ok2174
theorem ok2175 : andB (check start2175 proof2175) (cpOk (replay start2175 proof2175) start2176) = true := by
  decide +kernel
#print axioms ok2175
end Snake9.ReplayFull161
