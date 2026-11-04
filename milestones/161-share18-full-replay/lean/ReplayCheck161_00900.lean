import ReplayData161_0028
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

namespace Snake9.ReplayFull161
open Snake9.Lrat144 (andB)
open Snake9.LratFast144
theorem ok900 : check start900 proof900 = true := by
  decide +kernel
#print axioms ok900
theorem ok901 : check start901 proof901 = true := by
  decide +kernel
#print axioms ok901
theorem ok902 : check start902 proof902 = true := by
  decide +kernel
#print axioms ok902
theorem ok903 : check start903 proof903 = true := by
  decide +kernel
#print axioms ok903
end Snake9.ReplayFull161
