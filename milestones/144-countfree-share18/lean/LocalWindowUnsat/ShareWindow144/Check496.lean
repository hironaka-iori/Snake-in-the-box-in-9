import LocalWindowUnsat.ShareWindow144.Data496
import LocalWindowUnsat.ShareWindow144.Data497

/-! Kernel checks of segments 1981-1984 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok1981 : check start1981 proof1981 = true := by
  decide +kernel

theorem ok1982 : check start1982 proof1982 = true := by
  decide +kernel

theorem ok1983 : check start1983 proof1983 = true := by
  decide +kernel

theorem ok1984 : andB (check start1984 proof1984) (cpOk (replay start1984 proof1984) start1985) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
