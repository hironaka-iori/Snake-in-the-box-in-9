import Refined112.LocalWindowUnsat.Sum3142.Data6
import Refined112.LocalWindowUnsat.Sum3142.Data7

/-! Kernel checks of segments 21-24 of `sum3142` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.Sum3142
open Snake9.LratFast
open Snake9.Lrat (Tree TreeTrue andB)

theorem ok21 : check start21 proof21 = true := by
  decide +kernel

theorem ok22 : check start22 proof22 = true := by
  decide +kernel

theorem ok23 : check start23 proof23 = true := by
  decide +kernel

theorem ok24 : andB (check start24 proof24) (cpOk (replay start24 proof24) start25) = true := by
  decide +kernel

end Snake9.LocalWindow.Sum3142
