import LocalWindowUnsat.C323FwdDistinct.Data180

/-! Kernel checks of segments 177-180 of `323_fwd_distinct` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.C323FwdDistinct
open Snake9.Lrat

theorem ok177 : andB (check start177 proof177) (cpOk (replay start177 proof177) cp178) = true := by
  decide +kernel

theorem ok178 : check start178 proof178 = true := by
  decide +kernel

theorem ok179 : check start179 proof179 = true := by
  decide +kernel

theorem ok180 : andB (check start180 proof180) (hasEmpty (replay start180 proof180) 2602) = true := by
  decide +kernel

end Snake9.LocalWindow.C323FwdDistinct
