import ReplayData161_0018
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

namespace Snake9.ReplayFull161
open Snake9.Lrat144 (andB)
open Snake9.LratFast144
theorem ok600 : check start600 proof600 = true := by
  decide +kernel
#print axioms ok600
theorem ok601 : check start601 proof601 = true := by
  decide +kernel
#print axioms ok601
theorem ok602 : check start602 proof602 = true := by
  decide +kernel
#print axioms ok602
theorem ok603 : check start603 proof603 = true := by
  decide +kernel
#print axioms ok603
end Snake9.ReplayFull161
