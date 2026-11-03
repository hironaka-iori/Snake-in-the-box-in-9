import LocalWindowUnsat.ShareWindow144.Data521
import LocalWindowUnsat.ShareWindow144.Data522

/-! Kernel checks of segments 2081-2084 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok2081 : check start2081 proof2081 = true := by
  decide +kernel

theorem ok2082 : check start2082 proof2082 = true := by
  decide +kernel

theorem ok2083 : check start2083 proof2083 = true := by
  decide +kernel

theorem ok2084 : andB (check start2084 proof2084) (cpOk (replay start2084 proof2084) start2085) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
