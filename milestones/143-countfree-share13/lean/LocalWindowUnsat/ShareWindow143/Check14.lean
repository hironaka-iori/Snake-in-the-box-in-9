import LocalWindowUnsat.ShareWindow143.Data14
import LocalWindowUnsat.ShareWindow143.Data15

/-! Kernel checks of segments 53-56 of `share143` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow143
open Snake9.LratFast143
open Snake9.Lrat143 (Tree TreeTrue andB)

theorem ok53 : check start53 proof53 = true := by
  decide +kernel

theorem ok54 : check start54 proof54 = true := by
  decide +kernel

theorem ok55 : check start55 proof55 = true := by
  decide +kernel

theorem ok56 : andB (check start56 proof56) (cpOk (replay start56 proof56) start57) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow143
