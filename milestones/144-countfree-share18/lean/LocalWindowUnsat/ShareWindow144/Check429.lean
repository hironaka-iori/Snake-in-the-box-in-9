import LocalWindowUnsat.ShareWindow144.Data429
import LocalWindowUnsat.ShareWindow144.Data430

/-! Kernel checks of segments 1713-1716 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok1713 : check start1713 proof1713 = true := by
  decide +kernel

theorem ok1714 : check start1714 proof1714 = true := by
  decide +kernel

theorem ok1715 : check start1715 proof1715 = true := by
  decide +kernel

theorem ok1716 : andB (check start1716 proof1716) (cpOk (replay start1716 proof1716) start1717) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
