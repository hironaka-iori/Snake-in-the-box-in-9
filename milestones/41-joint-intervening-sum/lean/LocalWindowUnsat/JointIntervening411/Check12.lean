import LocalWindowUnsat.JointIntervening411.Data66
import LocalWindowUnsat.JointIntervening411.Data67
import LocalWindowUnsat.JointIntervening411.Data68
import LocalWindowUnsat.JointIntervening411.Data69
import LocalWindowUnsat.JointIntervening411.Data70
import LocalWindowUnsat.JointIntervening411.Data71
import LocalWindowUnsat.JointIntervening411.Data72

/-! Kernel checks of segments 67-72 of `sum411` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.JointIntervening411
open Snake9.LratFast
open Snake9.Lrat (Tree TreeTrue andB)

theorem ok67 : check start67 proof67 = true := by
  decide +kernel

theorem ok68 : andB (check start68 proof68) (cpOk (replay start68 proof68) start69) = true := by
  decide +kernel

theorem ok69 : check start69 proof69 = true := by
  decide +kernel

theorem ok70 : check start70 proof70 = true := by
  decide +kernel

theorem ok71 : check start71 proof71 = true := by
  decide +kernel

theorem ok72 : andB (check start72 proof72) (cpOk (replay start72 proof72) start73) = true := by
  decide +kernel

end Snake9.LocalWindow.JointIntervening411
