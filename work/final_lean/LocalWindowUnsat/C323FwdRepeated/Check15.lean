import LocalWindowUnsat.C323FwdRepeated.Data60

/-! Kernel checks of segments 57-60 of `323_fwd_repeated` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.C323FwdRepeated
open Snake9.Lrat

theorem ok57 : andB (check start57 proof57) (cpOk (replay start57 proof57) cp58) = true := by
  decide +kernel

theorem ok58 : check start58 proof58 = true := by
  decide +kernel

theorem ok59 : check start59 proof59 = true := by
  decide +kernel

theorem ok60 : andB (check start60 proof60) (cpOk (replay start60 proof60) cp61) = true := by
  decide +kernel

end Snake9.LocalWindow.C323FwdRepeated
