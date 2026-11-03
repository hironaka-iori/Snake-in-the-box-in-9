import LocalWindowUnsat.ShareWindow144.Data468
import LocalWindowUnsat.ShareWindow144.Data469

/-! Kernel checks of segments 1869-1872 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok1869 : check start1869 proof1869 = true := by
  decide +kernel

theorem ok1870 : check start1870 proof1870 = true := by
  decide +kernel

theorem ok1871 : check start1871 proof1871 = true := by
  decide +kernel

theorem ok1872 : andB (check start1872 proof1872) (cpOk (replay start1872 proof1872) start1873) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
