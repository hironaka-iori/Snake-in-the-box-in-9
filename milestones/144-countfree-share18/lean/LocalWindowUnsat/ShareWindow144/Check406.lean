import LocalWindowUnsat.ShareWindow144.Data406
import LocalWindowUnsat.ShareWindow144.Data407

/-! Kernel checks of segments 1621-1624 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok1621 : check start1621 proof1621 = true := by
  decide +kernel

theorem ok1622 : check start1622 proof1622 = true := by
  decide +kernel

theorem ok1623 : check start1623 proof1623 = true := by
  decide +kernel

theorem ok1624 : andB (check start1624 proof1624) (cpOk (replay start1624 proof1624) start1625) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
