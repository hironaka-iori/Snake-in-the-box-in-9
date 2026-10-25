import LocalWindowUnsat.JointIntervening501.Data306
import LocalWindowUnsat.JointIntervening501.Data307
import LocalWindowUnsat.JointIntervening501.Data308
import LocalWindowUnsat.JointIntervening501.Data309
import LocalWindowUnsat.JointIntervening501.Data310
import LocalWindowUnsat.JointIntervening501.Data311
import LocalWindowUnsat.JointIntervening501.Data312

/-! Kernel checks of segments 307-312 of `sum501` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.JointIntervening501
open Snake9.LratFast14
open Snake9.Lrat (Tree TreeTrue andB)

theorem ok307 : check start307 proof307 = true := by
  decide +kernel

theorem ok308 : andB (check start308 proof308) (cpOk (replay start308 proof308) start309) = true := by
  decide +kernel

theorem ok309 : check start309 proof309 = true := by
  decide +kernel

theorem ok310 : check start310 proof310 = true := by
  decide +kernel

theorem ok311 : check start311 proof311 = true := by
  decide +kernel

theorem ok312 : andB (check start312 proof312) (cpOk (replay start312 proof312) start313) = true := by
  decide +kernel

end Snake9.LocalWindow.JointIntervening501
