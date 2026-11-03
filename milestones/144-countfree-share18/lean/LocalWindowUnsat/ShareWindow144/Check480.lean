import LocalWindowUnsat.ShareWindow144.Data480
import LocalWindowUnsat.ShareWindow144.Data481

/-! Kernel checks of segments 1917-1920 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok1917 : check start1917 proof1917 = true := by
  decide +kernel

theorem ok1918 : check start1918 proof1918 = true := by
  decide +kernel

theorem ok1919 : check start1919 proof1919 = true := by
  decide +kernel

theorem ok1920 : andB (check start1920 proof1920) (cpOk (replay start1920 proof1920) start1921) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
