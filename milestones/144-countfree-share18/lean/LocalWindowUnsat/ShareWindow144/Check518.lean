import LocalWindowUnsat.ShareWindow144.Data518
import LocalWindowUnsat.ShareWindow144.Data519

/-! Kernel checks of segments 2069-2072 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok2069 : check start2069 proof2069 = true := by
  decide +kernel

theorem ok2070 : check start2070 proof2070 = true := by
  decide +kernel

theorem ok2071 : check start2071 proof2071 = true := by
  decide +kernel

theorem ok2072 : andB (check start2072 proof2072) (cpOk (replay start2072 proof2072) start2073) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
