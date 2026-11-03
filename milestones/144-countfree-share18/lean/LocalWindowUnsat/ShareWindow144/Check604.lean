import LocalWindowUnsat.ShareWindow144.Data604

/-! Kernel checks of segments 2413-2416 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok2413 : check start2413 proof2413 = true := by
  decide +kernel

theorem ok2414 : check start2414 proof2414 = true := by
  decide +kernel

theorem ok2415 : check start2415 proof2415 = true := by
  decide +kernel

theorem ok2416 : andB (check start2416 proof2416) (hasEmpty (replay start2416 proof2416) 8192) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
