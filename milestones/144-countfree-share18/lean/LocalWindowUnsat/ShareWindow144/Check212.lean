import LocalWindowUnsat.ShareWindow144.Data212
import LocalWindowUnsat.ShareWindow144.Data213

/-! Kernel checks of segments 845-848 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok845 : check start845 proof845 = true := by
  decide +kernel

theorem ok846 : check start846 proof846 = true := by
  decide +kernel

theorem ok847 : check start847 proof847 = true := by
  decide +kernel

theorem ok848 : andB (check start848 proof848) (cpOk (replay start848 proof848) start849) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
