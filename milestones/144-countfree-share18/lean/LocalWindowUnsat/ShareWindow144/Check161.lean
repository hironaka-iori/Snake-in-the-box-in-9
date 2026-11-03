import LocalWindowUnsat.ShareWindow144.Data161
import LocalWindowUnsat.ShareWindow144.Data162

/-! Kernel checks of segments 641-644 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok641 : check start641 proof641 = true := by
  decide +kernel

theorem ok642 : check start642 proof642 = true := by
  decide +kernel

theorem ok643 : check start643 proof643 = true := by
  decide +kernel

theorem ok644 : andB (check start644 proof644) (cpOk (replay start644 proof644) start645) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
