import ReplayData161_0028
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

namespace Snake9.ReplayFull161
open Snake9.Lrat144 (andB)
open Snake9.LratFast144
theorem ok924 : check start924 proof924 = true := by
  decide +kernel
#print axioms ok924
theorem ok925 : check start925 proof925 = true := by
  decide +kernel
#print axioms ok925
theorem ok926 : check start926 proof926 = true := by
  decide +kernel
#print axioms ok926
theorem ok927 : andB (check start927 proof927) (cpOk (replay start927 proof927) start928) = true := by
  decide +kernel
#print axioms ok927
end Snake9.ReplayFull161
