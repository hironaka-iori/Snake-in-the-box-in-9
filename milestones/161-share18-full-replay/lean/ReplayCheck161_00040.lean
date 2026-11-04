import ReplayData161_0001
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

namespace Snake9.ReplayFull161
open Snake9.Lrat144 (andB)
open Snake9.LratFast144
theorem ok40 : check start40 proof40 = true := by
  decide +kernel
#print axioms ok40
theorem ok41 : check start41 proof41 = true := by
  decide +kernel
#print axioms ok41
theorem ok42 : check start42 proof42 = true := by
  decide +kernel
#print axioms ok42
theorem ok43 : check start43 proof43 = true := by
  decide +kernel
#print axioms ok43
end Snake9.ReplayFull161
