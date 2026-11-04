import ReplayData161_0025
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

namespace Snake9.ReplayFull161
open Snake9.Lrat144 (andB)
open Snake9.LratFast144
theorem ok828 : check start828 proof828 = true := by
  decide +kernel
#print axioms ok828
theorem ok829 : check start829 proof829 = true := by
  decide +kernel
#print axioms ok829
theorem ok830 : check start830 proof830 = true := by
  decide +kernel
#print axioms ok830
theorem ok831 : andB (check start831 proof831) (cpOk (replay start831 proof831) start832) = true := by
  decide +kernel
#print axioms ok831
end Snake9.ReplayFull161
