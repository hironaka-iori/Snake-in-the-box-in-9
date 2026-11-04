import ReplayData161_0016
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

namespace Snake9.ReplayFull161
open Snake9.Lrat144 (andB)
open Snake9.LratFast144
theorem ok512 : check start512 proof512 = true := by
  decide +kernel
#print axioms ok512
theorem ok513 : check start513 proof513 = true := by
  decide +kernel
#print axioms ok513
theorem ok514 : check start514 proof514 = true := by
  decide +kernel
#print axioms ok514
theorem ok515 : check start515 proof515 = true := by
  decide +kernel
#print axioms ok515
end Snake9.ReplayFull161
