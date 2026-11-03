import LocalWindowUnsat.ShareWindow144.Data221
import LocalWindowUnsat.ShareWindow144.Data222

/-! Kernel checks of segments 881-884 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok881 : check start881 proof881 = true := by
  decide +kernel

theorem ok882 : check start882 proof882 = true := by
  decide +kernel

theorem ok883 : check start883 proof883 = true := by
  decide +kernel

theorem ok884 : andB (check start884 proof884) (cpOk (replay start884 proof884) start885) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
