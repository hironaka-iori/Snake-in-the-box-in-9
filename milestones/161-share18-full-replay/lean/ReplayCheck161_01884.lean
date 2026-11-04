import ReplayData161_0058
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

namespace Snake9.ReplayFull161
open Snake9.Lrat144 (andB)
open Snake9.LratFast144
theorem ok1884 : check start1884 proof1884 = true := by
  decide +kernel
#print axioms ok1884
theorem ok1885 : check start1885 proof1885 = true := by
  decide +kernel
#print axioms ok1885
theorem ok1886 : check start1886 proof1886 = true := by
  decide +kernel
#print axioms ok1886
theorem ok1887 : andB (check start1887 proof1887) (cpOk (replay start1887 proof1887) start1888) = true := by
  decide +kernel
#print axioms ok1887
end Snake9.ReplayFull161
