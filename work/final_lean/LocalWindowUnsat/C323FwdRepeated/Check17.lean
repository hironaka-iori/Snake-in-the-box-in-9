import LocalWindowUnsat.C323FwdRepeated.Data67

/-! Kernel checks of segments 65-67 of `323_fwd_repeated` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.C323FwdRepeated
open Snake9.Lrat

theorem ok65 : check start65 proof65 = true := by
  decide +kernel

theorem ok66 : andB (check start66 proof66) (cpOk (replay start66 proof66) cp67) = true := by
  decide +kernel

theorem ok67 : andB (check start67 proof67) (hasEmpty (replay start67 proof67) 1688) = true := by
  decide +kernel

end Snake9.LocalWindow.C323FwdRepeated
