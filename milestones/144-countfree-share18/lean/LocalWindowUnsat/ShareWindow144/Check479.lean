import LocalWindowUnsat.ShareWindow144.Data479
import LocalWindowUnsat.ShareWindow144.Data480

/-! Kernel checks of segments 1913-1916 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok1913 : check start1913 proof1913 = true := by
  decide +kernel

theorem ok1914 : check start1914 proof1914 = true := by
  decide +kernel

theorem ok1915 : check start1915 proof1915 = true := by
  decide +kernel

theorem ok1916 : andB (check start1916 proof1916) (cpOk (replay start1916 proof1916) start1917) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
