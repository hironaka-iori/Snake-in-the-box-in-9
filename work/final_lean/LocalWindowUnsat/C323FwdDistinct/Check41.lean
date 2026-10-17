import LocalWindowUnsat.C323FwdDistinct.Data164

/-! Kernel checks of segments 161-164 of `323_fwd_distinct` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.C323FwdDistinct
open Snake9.Lrat

theorem ok161 : check start161 proof161 = true := by
  decide +kernel

theorem ok162 : andB (check start162 proof162) (cpOk (replay start162 proof162) cp163) = true := by
  decide +kernel

theorem ok163 : check start163 proof163 = true := by
  decide +kernel

theorem ok164 : check start164 proof164 = true := by
  decide +kernel

end Snake9.LocalWindow.C323FwdDistinct
