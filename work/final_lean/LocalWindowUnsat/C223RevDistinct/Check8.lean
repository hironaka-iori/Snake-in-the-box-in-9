import LocalWindowUnsat.C223RevDistinct.Data31

/-! Kernel checks of segments 29-31 of `223_rev_distinct` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.C223RevDistinct
open Snake9.Lrat

theorem ok29 : check start29 proof29 = true := by
  decide +kernel

theorem ok30 : andB (check start30 proof30) (cpOk (replay start30 proof30) cp31) = true := by
  decide +kernel

theorem ok31 : andB (check start31 proof31) (hasEmpty (replay start31 proof31) 1118) = true := by
  decide +kernel

end Snake9.LocalWindow.C223RevDistinct
