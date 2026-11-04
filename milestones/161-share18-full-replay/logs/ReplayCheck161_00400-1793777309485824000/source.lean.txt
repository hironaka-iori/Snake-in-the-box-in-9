import ReplayData161_0012
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

namespace Snake9.ReplayFull161
open Snake9.Lrat144 (andB)
open Snake9.LratFast144
theorem ok400 : check start400 proof400 = true := by
  decide +kernel
#print axioms ok400
theorem ok401 : check start401 proof401 = true := by
  decide +kernel
#print axioms ok401
theorem ok402 : check start402 proof402 = true := by
  decide +kernel
#print axioms ok402
theorem ok403 : check start403 proof403 = true := by
  decide +kernel
#print axioms ok403
end Snake9.ReplayFull161
