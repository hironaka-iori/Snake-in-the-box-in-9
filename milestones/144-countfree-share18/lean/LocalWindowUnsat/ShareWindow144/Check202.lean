import LocalWindowUnsat.ShareWindow144.Data202
import LocalWindowUnsat.ShareWindow144.Data203

/-! Kernel checks of segments 805-808 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok805 : check start805 proof805 = true := by
  decide +kernel

theorem ok806 : check start806 proof806 = true := by
  decide +kernel

theorem ok807 : check start807 proof807 = true := by
  decide +kernel

theorem ok808 : andB (check start808 proof808) (cpOk (replay start808 proof808) start809) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
