import LocalWindowUnsat.SixFour10.Data53
import LocalWindowUnsat.SixFour10.Data54

/-! Kernel checks of segments 313-318 of `four10` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.SixFour10
open Snake9.LratFast
open Snake9.Lrat (Tree TreeTrue andB)

theorem ok313 : check start313 proof313 = true := by
  decide +kernel

theorem ok314 : check start314 proof314 = true := by
  decide +kernel

theorem ok315 : check start315 proof315 = true := by
  decide +kernel

theorem ok316 : check start316 proof316 = true := by
  decide +kernel

theorem ok317 : check start317 proof317 = true := by
  decide +kernel

theorem ok318 : andB (check start318 proof318) (cpOk (replay start318 proof318) start319) = true := by
  decide +kernel

end Snake9.LocalWindow.SixFour10
