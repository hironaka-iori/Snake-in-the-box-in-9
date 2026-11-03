import LocalWindowUnsat.ShareWindow144.Data227
import LocalWindowUnsat.ShareWindow144.Data228

/-! Kernel checks of segments 905-908 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok905 : check start905 proof905 = true := by
  decide +kernel

theorem ok906 : check start906 proof906 = true := by
  decide +kernel

theorem ok907 : check start907 proof907 = true := by
  decide +kernel

theorem ok908 : andB (check start908 proof908) (cpOk (replay start908 proof908) start909) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
