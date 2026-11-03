import LocalWindowUnsat.ShareWindow144.Data478
import LocalWindowUnsat.ShareWindow144.Data479

/-! Kernel checks of segments 1909-1912 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok1909 : check start1909 proof1909 = true := by
  decide +kernel

theorem ok1910 : check start1910 proof1910 = true := by
  decide +kernel

theorem ok1911 : check start1911 proof1911 = true := by
  decide +kernel

theorem ok1912 : andB (check start1912 proof1912) (cpOk (replay start1912 proof1912) start1913) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
