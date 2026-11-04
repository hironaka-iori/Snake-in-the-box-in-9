import ReplayData161_0051
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

namespace Snake9.ReplayFull161
open Snake9.Lrat144 (andB)
open Snake9.LratFast144
theorem ok1660 : check start1660 proof1660 = true := by
  decide +kernel
#print axioms ok1660
theorem ok1661 : check start1661 proof1661 = true := by
  decide +kernel
#print axioms ok1661
theorem ok1662 : check start1662 proof1662 = true := by
  decide +kernel
#print axioms ok1662
theorem ok1663 : andB (check start1663 proof1663) (cpOk (replay start1663 proof1663) start1664) = true := by
  decide +kernel
#print axioms ok1663
end Snake9.ReplayFull161
