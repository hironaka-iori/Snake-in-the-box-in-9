import LocalWindowUnsat.End35.Data39
import LocalWindowUnsat.End35.Data40

/-! Kernel checks of segments 229-234 of `end35` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.End35
open Snake9.LratFastEndpoint122
open Snake9.Lrat (Tree TreeTrue andB)

theorem ok229 : check start229 proof229 = true := by
  decide +kernel

theorem ok230 : check start230 proof230 = true := by
  decide +kernel

theorem ok231 : check start231 proof231 = true := by
  decide +kernel

theorem ok232 : check start232 proof232 = true := by
  decide +kernel

theorem ok233 : check start233 proof233 = true := by
  decide +kernel

theorem ok234 : andB (check start234 proof234) (cpOk (replay start234 proof234) start235) = true := by
  decide +kernel

end Snake9.LocalWindow.End35
