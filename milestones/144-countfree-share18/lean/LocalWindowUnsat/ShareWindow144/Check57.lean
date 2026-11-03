import LocalWindowUnsat.ShareWindow144.Data57
import LocalWindowUnsat.ShareWindow144.Data58

/-! Kernel checks of segments 225-228 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok225 : check start225 proof225 = true := by
  decide +kernel

theorem ok226 : check start226 proof226 = true := by
  decide +kernel

theorem ok227 : check start227 proof227 = true := by
  decide +kernel

theorem ok228 : andB (check start228 proof228) (cpOk (replay start228 proof228) start229) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
