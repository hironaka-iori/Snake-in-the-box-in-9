import LocalWindowUnsat.ShareWindow144.Data405
import LocalWindowUnsat.ShareWindow144.Data406

/-! Kernel checks of segments 1617-1620 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok1617 : check start1617 proof1617 = true := by
  decide +kernel

theorem ok1618 : check start1618 proof1618 = true := by
  decide +kernel

theorem ok1619 : check start1619 proof1619 = true := by
  decide +kernel

theorem ok1620 : andB (check start1620 proof1620) (cpOk (replay start1620 proof1620) start1621) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
