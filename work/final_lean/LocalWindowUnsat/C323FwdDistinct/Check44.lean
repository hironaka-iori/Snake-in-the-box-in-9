import LocalWindowUnsat.C323FwdDistinct.Data176

/-! Kernel checks of segments 173-176 of `323_fwd_distinct` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.C323FwdDistinct
open Snake9.Lrat

theorem ok173 : check start173 proof173 = true := by
  decide +kernel

theorem ok174 : andB (check start174 proof174) (cpOk (replay start174 proof174) cp175) = true := by
  decide +kernel

theorem ok175 : check start175 proof175 = true := by
  decide +kernel

theorem ok176 : check start176 proof176 = true := by
  decide +kernel

end Snake9.LocalWindow.C323FwdDistinct
