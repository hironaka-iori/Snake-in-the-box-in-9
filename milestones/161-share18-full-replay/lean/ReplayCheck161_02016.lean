import ReplayData161_0063
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

namespace Snake9.ReplayFull161
open Snake9.Lrat144 (andB)
open Snake9.LratFast144
theorem ok2016 : check start2016 proof2016 = true := by
  decide +kernel
#print axioms ok2016
theorem ok2017 : check start2017 proof2017 = true := by
  decide +kernel
#print axioms ok2017
theorem ok2018 : check start2018 proof2018 = true := by
  decide +kernel
#print axioms ok2018
theorem ok2019 : check start2019 proof2019 = true := by
  decide +kernel
#print axioms ok2019
end Snake9.ReplayFull161
