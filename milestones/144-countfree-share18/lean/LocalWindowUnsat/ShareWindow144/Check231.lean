import LocalWindowUnsat.ShareWindow144.Data231
import LocalWindowUnsat.ShareWindow144.Data232

/-! Kernel checks of segments 921-924 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok921 : check start921 proof921 = true := by
  decide +kernel

theorem ok922 : check start922 proof922 = true := by
  decide +kernel

theorem ok923 : check start923 proof923 = true := by
  decide +kernel

theorem ok924 : andB (check start924 proof924) (cpOk (replay start924 proof924) start925) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
