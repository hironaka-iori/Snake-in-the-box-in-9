import LocalWindowUnsat.C323FwdDistinct.Data100

/-! Kernel checks of segments 97-100 of `323_fwd_distinct` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.C323FwdDistinct
open Snake9.Lrat

theorem ok97 : check start97 proof97 = true := by
  decide +kernel

theorem ok98 : check start98 proof98 = true := by
  decide +kernel

theorem ok99 : andB (check start99 proof99) (cpOk (replay start99 proof99) cp100) = true := by
  decide +kernel

theorem ok100 : check start100 proof100 = true := by
  decide +kernel

end Snake9.LocalWindow.C323FwdDistinct
