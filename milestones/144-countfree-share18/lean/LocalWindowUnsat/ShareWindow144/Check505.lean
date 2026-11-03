import LocalWindowUnsat.ShareWindow144.Data505
import LocalWindowUnsat.ShareWindow144.Data506

/-! Kernel checks of segments 2017-2020 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok2017 : check start2017 proof2017 = true := by
  decide +kernel

theorem ok2018 : check start2018 proof2018 = true := by
  decide +kernel

theorem ok2019 : check start2019 proof2019 = true := by
  decide +kernel

theorem ok2020 : andB (check start2020 proof2020) (cpOk (replay start2020 proof2020) start2021) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
