import LocalWindowUnsat.ShareWindow143.Data7
import LocalWindowUnsat.ShareWindow143.Data8

/-! Kernel checks of segments 25-28 of `share143` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow143
open Snake9.LratFast143
open Snake9.Lrat143 (Tree TreeTrue andB)

theorem ok25 : check start25 proof25 = true := by
  decide +kernel

theorem ok26 : check start26 proof26 = true := by
  decide +kernel

theorem ok27 : check start27 proof27 = true := by
  decide +kernel

theorem ok28 : andB (check start28 proof28) (cpOk (replay start28 proof28) start29) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow143
