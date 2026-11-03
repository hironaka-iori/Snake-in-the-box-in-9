import LocalWindowUnsat.ShareWindow144.Data407
import LocalWindowUnsat.ShareWindow144.Data408

/-! Kernel checks of segments 1625-1628 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok1625 : check start1625 proof1625 = true := by
  decide +kernel

theorem ok1626 : check start1626 proof1626 = true := by
  decide +kernel

theorem ok1627 : check start1627 proof1627 = true := by
  decide +kernel

theorem ok1628 : andB (check start1628 proof1628) (cpOk (replay start1628 proof1628) start1629) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
