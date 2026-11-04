import ReplayData161_0025
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

namespace Snake9.ReplayFull161
open Snake9.Lrat144 (andB)
open Snake9.LratFast144
theorem ok800 : check start800 proof800 = true := by
  decide +kernel
#print axioms ok800
theorem ok801 : check start801 proof801 = true := by
  decide +kernel
#print axioms ok801
theorem ok802 : check start802 proof802 = true := by
  decide +kernel
#print axioms ok802
theorem ok803 : check start803 proof803 = true := by
  decide +kernel
#print axioms ok803
end Snake9.ReplayFull161
