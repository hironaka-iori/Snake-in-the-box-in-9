import LocalWindowUnsat.ShareWindow144.Data206
import LocalWindowUnsat.ShareWindow144.Data207

/-! Kernel checks of segments 821-824 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok821 : check start821 proof821 = true := by
  decide +kernel

theorem ok822 : check start822 proof822 = true := by
  decide +kernel

theorem ok823 : check start823 proof823 = true := by
  decide +kernel

theorem ok824 : andB (check start824 proof824) (cpOk (replay start824 proof824) start825) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
