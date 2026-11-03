import Recovered122G.LocalWindowUnsat.End44.Data12
import Recovered122G.LocalWindowUnsat.End44.Data13

/-! Kernel checks of segments 67-72 of `end44` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.End44
open Snake9.LratFastEndpoint122
open Snake9.Lrat (Tree TreeTrue andB)

theorem ok67 : check start67 proof67 = true := by
  decide +kernel

theorem ok68 : check start68 proof68 = true := by
  decide +kernel

theorem ok69 : check start69 proof69 = true := by
  decide +kernel

theorem ok70 : check start70 proof70 = true := by
  decide +kernel

theorem ok71 : check start71 proof71 = true := by
  decide +kernel

theorem ok72 : andB (check start72 proof72) (cpOk (replay start72 proof72) start73) = true := by
  decide +kernel

end Snake9.LocalWindow.End44
