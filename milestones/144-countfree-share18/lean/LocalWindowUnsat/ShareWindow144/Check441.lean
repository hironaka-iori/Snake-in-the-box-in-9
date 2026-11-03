import LocalWindowUnsat.ShareWindow144.Data441
import LocalWindowUnsat.ShareWindow144.Data442

/-! Kernel checks of segments 1761-1764 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok1761 : check start1761 proof1761 = true := by
  decide +kernel

theorem ok1762 : check start1762 proof1762 = true := by
  decide +kernel

theorem ok1763 : check start1763 proof1763 = true := by
  decide +kernel

theorem ok1764 : andB (check start1764 proof1764) (cpOk (replay start1764 proof1764) start1765) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
