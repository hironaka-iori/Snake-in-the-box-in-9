import LocalWindowUnsat.ShareWindow144.Data434
import LocalWindowUnsat.ShareWindow144.Data435

/-! Kernel checks of segments 1733-1736 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok1733 : check start1733 proof1733 = true := by
  decide +kernel

theorem ok1734 : check start1734 proof1734 = true := by
  decide +kernel

theorem ok1735 : check start1735 proof1735 = true := by
  decide +kernel

theorem ok1736 : andB (check start1736 proof1736) (cpOk (replay start1736 proof1736) start1737) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
