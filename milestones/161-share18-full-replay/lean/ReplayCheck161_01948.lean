import ReplayData161_0060
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

namespace Snake9.ReplayFull161
open Snake9.Lrat144 (andB)
open Snake9.LratFast144
theorem ok1948 : check start1948 proof1948 = true := by
  decide +kernel
#print axioms ok1948
theorem ok1949 : check start1949 proof1949 = true := by
  decide +kernel
#print axioms ok1949
theorem ok1950 : check start1950 proof1950 = true := by
  decide +kernel
#print axioms ok1950
theorem ok1951 : andB (check start1951 proof1951) (cpOk (replay start1951 proof1951) start1952) = true := by
  decide +kernel
#print axioms ok1951
end Snake9.ReplayFull161
