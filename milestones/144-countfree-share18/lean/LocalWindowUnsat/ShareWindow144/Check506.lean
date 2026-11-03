import LocalWindowUnsat.ShareWindow144.Data506
import LocalWindowUnsat.ShareWindow144.Data507

/-! Kernel checks of segments 2021-2024 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok2021 : check start2021 proof2021 = true := by
  decide +kernel

theorem ok2022 : check start2022 proof2022 = true := by
  decide +kernel

theorem ok2023 : check start2023 proof2023 = true := by
  decide +kernel

theorem ok2024 : andB (check start2024 proof2024) (cpOk (replay start2024 proof2024) start2025) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
