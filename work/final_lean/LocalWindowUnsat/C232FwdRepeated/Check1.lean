import LocalWindowUnsat.C232FwdRepeated.Data3

/-! Kernel checks of segments 1-3 of `232_fwd_repeated` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.C232FwdRepeated
open Snake9.Lrat

theorem ok1 : check start1 proof1 = true := by
  decide +kernel

theorem ok2 : check start2 proof2 = true := by
  decide +kernel

theorem ok3 : andB (check start3 proof3) (hasEmpty (replay start3 proof3) 663) = true := by
  decide +kernel

end Snake9.LocalWindow.C232FwdRepeated
