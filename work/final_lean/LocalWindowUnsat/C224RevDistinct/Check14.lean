import LocalWindowUnsat.C224RevDistinct.Data55

/-! Kernel checks of segments 53-55 of `224_rev_distinct` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.C224RevDistinct
open Snake9.Lrat

theorem ok53 : check start53 proof53 = true := by
  decide +kernel

theorem ok54 : andB (check start54 proof54) (cpOk (replay start54 proof54) cp55) = true := by
  decide +kernel

theorem ok55 : andB (check start55 proof55) (hasEmpty (replay start55 proof55) 1496) = true := by
  decide +kernel

end Snake9.LocalWindow.C224RevDistinct
