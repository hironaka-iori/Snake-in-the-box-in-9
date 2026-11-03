import LocalWindowUnsat.SixFour10.Data69
import LocalWindowUnsat.SixFour10.Data70

/-! Kernel checks of segments 409-414 of `four10` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.SixFour10
open Snake9.LratFast
open Snake9.Lrat (Tree TreeTrue andB)

theorem ok409 : check start409 proof409 = true := by
  decide +kernel

theorem ok410 : check start410 proof410 = true := by
  decide +kernel

theorem ok411 : check start411 proof411 = true := by
  decide +kernel

theorem ok412 : check start412 proof412 = true := by
  decide +kernel

theorem ok413 : check start413 proof413 = true := by
  decide +kernel

theorem ok414 : andB (check start414 proof414) (cpOk (replay start414 proof414) start415) = true := by
  decide +kernel

end Snake9.LocalWindow.SixFour10
