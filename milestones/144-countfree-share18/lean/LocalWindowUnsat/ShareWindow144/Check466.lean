import LocalWindowUnsat.ShareWindow144.Data466
import LocalWindowUnsat.ShareWindow144.Data467

/-! Kernel checks of segments 1861-1864 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok1861 : check start1861 proof1861 = true := by
  decide +kernel

theorem ok1862 : check start1862 proof1862 = true := by
  decide +kernel

theorem ok1863 : check start1863 proof1863 = true := by
  decide +kernel

theorem ok1864 : andB (check start1864 proof1864) (cpOk (replay start1864 proof1864) start1865) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
