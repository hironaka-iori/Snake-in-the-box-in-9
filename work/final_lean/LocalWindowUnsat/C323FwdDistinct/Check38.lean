import LocalWindowUnsat.C323FwdDistinct.Data152

/-! Kernel checks of segments 149-152 of `323_fwd_distinct` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.C323FwdDistinct
open Snake9.Lrat

theorem ok149 : check start149 proof149 = true := by
  decide +kernel

theorem ok150 : andB (check start150 proof150) (cpOk (replay start150 proof150) cp151) = true := by
  decide +kernel

theorem ok151 : check start151 proof151 = true := by
  decide +kernel

theorem ok152 : check start152 proof152 = true := by
  decide +kernel

end Snake9.LocalWindow.C323FwdDistinct
