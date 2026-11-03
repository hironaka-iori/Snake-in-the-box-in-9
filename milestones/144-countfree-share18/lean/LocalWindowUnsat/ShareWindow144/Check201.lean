import LocalWindowUnsat.ShareWindow144.Data201
import LocalWindowUnsat.ShareWindow144.Data202

/-! Kernel checks of segments 801-804 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok801 : check start801 proof801 = true := by
  decide +kernel

theorem ok802 : check start802 proof802 = true := by
  decide +kernel

theorem ok803 : check start803 proof803 = true := by
  decide +kernel

theorem ok804 : andB (check start804 proof804) (cpOk (replay start804 proof804) start805) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
