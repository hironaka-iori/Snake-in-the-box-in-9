import LocalWindowUnsat.ShareWindow144.Data145
import LocalWindowUnsat.ShareWindow144.Data146

/-! Kernel checks of segments 577-580 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok577 : check start577 proof577 = true := by
  decide +kernel

theorem ok578 : check start578 proof578 = true := by
  decide +kernel

theorem ok579 : check start579 proof579 = true := by
  decide +kernel

theorem ok580 : andB (check start580 proof580) (cpOk (replay start580 proof580) start581) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
