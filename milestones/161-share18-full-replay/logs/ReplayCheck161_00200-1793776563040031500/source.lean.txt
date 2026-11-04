import ReplayData161_0006
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

namespace Snake9.ReplayFull161
open Snake9.Lrat144 (andB)
open Snake9.LratFast144
theorem ok200 : check start200 proof200 = true := by
  decide +kernel
#print axioms ok200
theorem ok201 : check start201 proof201 = true := by
  decide +kernel
#print axioms ok201
theorem ok202 : check start202 proof202 = true := by
  decide +kernel
#print axioms ok202
theorem ok203 : check start203 proof203 = true := by
  decide +kernel
#print axioms ok203
end Snake9.ReplayFull161
