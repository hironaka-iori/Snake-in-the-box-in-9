import LocalWindowUnsat.End35.Data52
import LocalWindowUnsat.End35.Data53

/-! Kernel checks of segments 307-312 of `end35` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.End35
open Snake9.LratFastEndpoint122
open Snake9.Lrat (Tree TreeTrue andB)

theorem ok307 : check start307 proof307 = true := by
  decide +kernel

theorem ok308 : check start308 proof308 = true := by
  decide +kernel

theorem ok309 : check start309 proof309 = true := by
  decide +kernel

theorem ok310 : check start310 proof310 = true := by
  decide +kernel

theorem ok311 : check start311 proof311 = true := by
  decide +kernel

theorem ok312 : andB (check start312 proof312) (cpOk (replay start312 proof312) start313) = true := by
  decide +kernel

end Snake9.LocalWindow.End35
