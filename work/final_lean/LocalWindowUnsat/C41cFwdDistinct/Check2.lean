import LocalWindowUnsat.C41cFwdDistinct.Data5

/-! Kernel checks of segments 5-5 of `41c_fwd_distinct` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.C41cFwdDistinct
open Snake9.Lrat

theorem ok5 : andB (check start5 proof5) (hasEmpty (replay start5 proof5) 512) = true := by
  decide +kernel

end Snake9.LocalWindow.C41cFwdDistinct
