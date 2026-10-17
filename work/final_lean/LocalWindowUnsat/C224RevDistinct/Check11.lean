import LocalWindowUnsat.C224RevDistinct.Data44

/-! Kernel checks of segments 41-44 of `224_rev_distinct` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.C224RevDistinct
open Snake9.Lrat

theorem ok41 : check start41 proof41 = true := by
  decide +kernel

theorem ok42 : andB (check start42 proof42) (cpOk (replay start42 proof42) cp43) = true := by
  decide +kernel

theorem ok43 : check start43 proof43 = true := by
  decide +kernel

theorem ok44 : check start44 proof44 = true := by
  decide +kernel

end Snake9.LocalWindow.C224RevDistinct
