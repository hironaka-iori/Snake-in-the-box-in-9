import LocalWindowUnsat.ShareWindow144.Data507
import LocalWindowUnsat.ShareWindow144.Data508

/-! Kernel checks of segments 2025-2028 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok2025 : check start2025 proof2025 = true := by
  decide +kernel

theorem ok2026 : check start2026 proof2026 = true := by
  decide +kernel

theorem ok2027 : check start2027 proof2027 = true := by
  decide +kernel

theorem ok2028 : andB (check start2028 proof2028) (cpOk (replay start2028 proof2028) start2029) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
