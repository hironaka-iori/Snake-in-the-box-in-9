import LocalWindowUnsat.ShareWindow144.Data465
import LocalWindowUnsat.ShareWindow144.Data466

/-! Kernel checks of segments 1857-1860 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok1857 : check start1857 proof1857 = true := by
  decide +kernel

theorem ok1858 : check start1858 proof1858 = true := by
  decide +kernel

theorem ok1859 : check start1859 proof1859 = true := by
  decide +kernel

theorem ok1860 : andB (check start1860 proof1860) (cpOk (replay start1860 proof1860) start1861) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
