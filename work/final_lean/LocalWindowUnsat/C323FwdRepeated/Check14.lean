import LocalWindowUnsat.C323FwdRepeated.Data56

/-! Kernel checks of segments 53-56 of `323_fwd_repeated` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.C323FwdRepeated
open Snake9.Lrat

theorem ok53 : check start53 proof53 = true := by
  decide +kernel

theorem ok54 : andB (check start54 proof54) (cpOk (replay start54 proof54) cp55) = true := by
  decide +kernel

theorem ok55 : check start55 proof55 = true := by
  decide +kernel

theorem ok56 : check start56 proof56 = true := by
  decide +kernel

end Snake9.LocalWindow.C323FwdRepeated
