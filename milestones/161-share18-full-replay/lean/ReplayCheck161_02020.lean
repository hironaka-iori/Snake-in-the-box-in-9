import ReplayData161_0063
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

namespace Snake9.ReplayFull161
open Snake9.Lrat144 (andB)
open Snake9.LratFast144
theorem ok2020 : check start2020 proof2020 = true := by
  decide +kernel
#print axioms ok2020
theorem ok2021 : check start2021 proof2021 = true := by
  decide +kernel
#print axioms ok2021
theorem ok2022 : check start2022 proof2022 = true := by
  decide +kernel
#print axioms ok2022
theorem ok2023 : check start2023 proof2023 = true := by
  decide +kernel
#print axioms ok2023
end Snake9.ReplayFull161
