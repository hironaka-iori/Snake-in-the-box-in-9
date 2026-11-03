import LocalWindowUnsat.ShareWindow144.Data453
import LocalWindowUnsat.ShareWindow144.Data454

/-! Kernel checks of segments 1809-1812 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok1809 : check start1809 proof1809 = true := by
  decide +kernel

theorem ok1810 : check start1810 proof1810 = true := by
  decide +kernel

theorem ok1811 : check start1811 proof1811 = true := by
  decide +kernel

theorem ok1812 : andB (check start1812 proof1812) (cpOk (replay start1812 proof1812) start1813) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
