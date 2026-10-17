import LocalWindowUnsat.C223FwdDistinct.Data38

/-! Kernel checks of segments 37-38 of `223_fwd_distinct` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.C223FwdDistinct
open Snake9.Lrat

theorem ok37 : check start37 proof37 = true := by
  decide +kernel

theorem ok38 : andB (check start38 proof38) (hasEmpty (replay start38 proof38) 1244) = true := by
  decide +kernel

end Snake9.LocalWindow.C223FwdDistinct
