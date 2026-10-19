import LocalWindowUnsat.C224RevRepeated.Data20

/-! Kernel checks of segments 17-20 of `224_rev_repeated` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.C224RevRepeated
open Snake9.Lrat

theorem ok17 : check start17 proof17 = true := by
  decide +kernel

theorem ok18 : andB (check start18 proof18) (cpOk (replay start18 proof18) cp19) = true := by
  decide +kernel

theorem ok19 : check start19 proof19 = true := by
  decide +kernel

theorem ok20 : check start20 proof20 = true := by
  decide +kernel

end Snake9.LocalWindow.C224RevRepeated
