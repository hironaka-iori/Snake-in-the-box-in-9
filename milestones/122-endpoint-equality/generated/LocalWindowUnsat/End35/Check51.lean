import LocalWindowUnsat.End35.Data51
import LocalWindowUnsat.End35.Data52

/-! Kernel checks of segments 301-306 of `end35` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.End35
open Snake9.LratFastEndpoint122
open Snake9.Lrat (Tree TreeTrue andB)

theorem ok301 : check start301 proof301 = true := by
  decide +kernel

theorem ok302 : check start302 proof302 = true := by
  decide +kernel

theorem ok303 : check start303 proof303 = true := by
  decide +kernel

theorem ok304 : check start304 proof304 = true := by
  decide +kernel

theorem ok305 : check start305 proof305 = true := by
  decide +kernel

theorem ok306 : andB (check start306 proof306) (cpOk (replay start306 proof306) start307) = true := by
  decide +kernel

end Snake9.LocalWindow.End35
