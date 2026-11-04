import ReplayData161_0000
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

namespace Snake9.ReplayFull161
open Snake9.Lrat144 (andB)
open Snake9.LratFast144
theorem ok8 : check start8 proof8 = true := by
  decide +kernel
#print axioms ok8
theorem ok9 : check start9 proof9 = true := by
  decide +kernel
#print axioms ok9
theorem ok10 : check start10 proof10 = true := by
  decide +kernel
#print axioms ok10
theorem ok11 : check start11 proof11 = true := by
  decide +kernel
#print axioms ok11
end Snake9.ReplayFull161
