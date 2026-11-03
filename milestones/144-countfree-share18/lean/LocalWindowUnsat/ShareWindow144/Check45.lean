import LocalWindowUnsat.ShareWindow144.Data45
import LocalWindowUnsat.ShareWindow144.Data46

/-! Kernel checks of segments 177-180 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok177 : check start177 proof177 = true := by
  decide +kernel

theorem ok178 : check start178 proof178 = true := by
  decide +kernel

theorem ok179 : check start179 proof179 = true := by
  decide +kernel

theorem ok180 : andB (check start180 proof180) (cpOk (replay start180 proof180) start181) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
