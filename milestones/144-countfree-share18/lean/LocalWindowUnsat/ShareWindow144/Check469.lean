import LocalWindowUnsat.ShareWindow144.Data469
import LocalWindowUnsat.ShareWindow144.Data470

/-! Kernel checks of segments 1873-1876 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok1873 : check start1873 proof1873 = true := by
  decide +kernel

theorem ok1874 : check start1874 proof1874 = true := by
  decide +kernel

theorem ok1875 : check start1875 proof1875 = true := by
  decide +kernel

theorem ok1876 : andB (check start1876 proof1876) (cpOk (replay start1876 proof1876) start1877) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
