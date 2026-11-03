import LocalWindowUnsat.ShareWindow144.Data431
import LocalWindowUnsat.ShareWindow144.Data432

/-! Kernel checks of segments 1721-1724 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok1721 : check start1721 proof1721 = true := by
  decide +kernel

theorem ok1722 : check start1722 proof1722 = true := by
  decide +kernel

theorem ok1723 : check start1723 proof1723 = true := by
  decide +kernel

theorem ok1724 : andB (check start1724 proof1724) (cpOk (replay start1724 proof1724) start1725) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
