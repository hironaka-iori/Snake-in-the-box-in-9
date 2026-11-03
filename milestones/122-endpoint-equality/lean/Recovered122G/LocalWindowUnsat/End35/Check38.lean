import Recovered122G.LocalWindowUnsat.End35.Data38
import Recovered122G.LocalWindowUnsat.End35.Data39

/-! Kernel checks of segments 223-228 of `end35` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.End35
open Snake9.LratFastEndpoint122
open Snake9.Lrat (Tree TreeTrue andB)

theorem ok223 : check start223 proof223 = true := by
  decide +kernel

theorem ok224 : check start224 proof224 = true := by
  decide +kernel

theorem ok225 : check start225 proof225 = true := by
  decide +kernel

theorem ok226 : check start226 proof226 = true := by
  decide +kernel

theorem ok227 : check start227 proof227 = true := by
  decide +kernel

theorem ok228 : andB (check start228 proof228) (cpOk (replay start228 proof228) start229) = true := by
  decide +kernel

end Snake9.LocalWindow.End35
