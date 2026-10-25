import LocalWindowUnsat.JointIntervening501.Data318
import LocalWindowUnsat.JointIntervening501.Data319
import LocalWindowUnsat.JointIntervening501.Data320
import LocalWindowUnsat.JointIntervening501.Data321
import LocalWindowUnsat.JointIntervening501.Data322
import LocalWindowUnsat.JointIntervening501.Data323
import LocalWindowUnsat.JointIntervening501.Data324

/-! Kernel checks of segments 319-324 of `sum501` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.JointIntervening501
open Snake9.LratFast14
open Snake9.Lrat (Tree TreeTrue andB)

theorem ok319 : check start319 proof319 = true := by
  decide +kernel

theorem ok320 : andB (check start320 proof320) (cpOk (replay start320 proof320) start321) = true := by
  decide +kernel

theorem ok321 : check start321 proof321 = true := by
  decide +kernel

theorem ok322 : check start322 proof322 = true := by
  decide +kernel

theorem ok323 : check start323 proof323 = true := by
  decide +kernel

theorem ok324 : andB (check start324 proof324) (cpOk (replay start324 proof324) start325) = true := by
  decide +kernel

end Snake9.LocalWindow.JointIntervening501
