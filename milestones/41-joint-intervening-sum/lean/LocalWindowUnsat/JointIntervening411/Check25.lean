import LocalWindowUnsat.JointIntervening411.Data144
import LocalWindowUnsat.JointIntervening411.Data145
import LocalWindowUnsat.JointIntervening411.Data146
import LocalWindowUnsat.JointIntervening411.Data147
import LocalWindowUnsat.JointIntervening411.Data148
import LocalWindowUnsat.JointIntervening411.Data149
import LocalWindowUnsat.JointIntervening411.Data150

/-! Kernel checks of segments 145-150 of `sum411` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.JointIntervening411
open Snake9.LratFast
open Snake9.Lrat (Tree TreeTrue andB)

theorem ok145 : check start145 proof145 = true := by
  decide +kernel

theorem ok146 : check start146 proof146 = true := by
  decide +kernel

theorem ok147 : check start147 proof147 = true := by
  decide +kernel

theorem ok148 : andB (check start148 proof148) (cpOk (replay start148 proof148) start149) = true := by
  decide +kernel

theorem ok149 : check start149 proof149 = true := by
  decide +kernel

theorem ok150 : check start150 proof150 = true := by
  decide +kernel

end Snake9.LocalWindow.JointIntervening411
