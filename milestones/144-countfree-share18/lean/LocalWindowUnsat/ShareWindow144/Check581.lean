import LocalWindowUnsat.ShareWindow144.Data581
import LocalWindowUnsat.ShareWindow144.Data582

/-! Kernel checks of segments 2321-2324 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok2321 : check start2321 proof2321 = true := by
  decide +kernel

theorem ok2322 : check start2322 proof2322 = true := by
  decide +kernel

theorem ok2323 : check start2323 proof2323 = true := by
  decide +kernel

theorem ok2324 : andB (check start2324 proof2324) (cpOk (replay start2324 proof2324) start2325) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
