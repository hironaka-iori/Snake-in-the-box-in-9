import ReplayData161_0026
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

namespace Snake9.ReplayFull161
open Snake9.Lrat144 (andB)
open Snake9.LratFast144
theorem ok860 : check start860 proof860 = true := by
  decide +kernel
#print axioms ok860
theorem ok861 : check start861 proof861 = true := by
  decide +kernel
#print axioms ok861
theorem ok862 : check start862 proof862 = true := by
  decide +kernel
#print axioms ok862
theorem ok863 : andB (check start863 proof863) (cpOk (replay start863 proof863) start864) = true := by
  decide +kernel
#print axioms ok863
end Snake9.ReplayFull161
