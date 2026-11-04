import ReplayData161_0002
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

namespace Snake9.ReplayFull161
open Snake9.Lrat144 (andB)
open Snake9.LratFast144
theorem ok64 : check start64 proof64 = true := by
  decide +kernel
#print axioms ok64
theorem ok65 : check start65 proof65 = true := by
  decide +kernel
#print axioms ok65
theorem ok66 : check start66 proof66 = true := by
  decide +kernel
#print axioms ok66
theorem ok67 : check start67 proof67 = true := by
  decide +kernel
#print axioms ok67
end Snake9.ReplayFull161
