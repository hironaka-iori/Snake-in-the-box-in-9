import LocalWindowUnsat.ShareWindow144.Data179
import LocalWindowUnsat.ShareWindow144.Data180

/-! Kernel checks of segments 713-716 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok713 : check start713 proof713 = true := by
  decide +kernel

theorem ok714 : check start714 proof714 = true := by
  decide +kernel

theorem ok715 : check start715 proof715 = true := by
  decide +kernel

theorem ok716 : andB (check start716 proof716) (cpOk (replay start716 proof716) start717) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
