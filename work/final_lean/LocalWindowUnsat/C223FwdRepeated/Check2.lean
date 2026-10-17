import LocalWindowUnsat.C223FwdRepeated.Data6

/-! Kernel checks of segments 5-6 of `223_fwd_repeated` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.C223FwdRepeated
open Snake9.Lrat

theorem ok5 : check start5 proof5 = true := by
  decide +kernel

theorem ok6 : andB (check start6 proof6) (hasEmpty (replay start6 proof6) 735) = true := by
  decide +kernel

end Snake9.LocalWindow.C223FwdRepeated
