import LocalWindowUnsat.ShareWindow143.Data48
import LocalWindowUnsat.ShareWindow143.Data49

/-! Kernel checks of segments 189-192 of `share143` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow143
open Snake9.LratFast143
open Snake9.Lrat143 (Tree TreeTrue andB)

theorem ok189 : check start189 proof189 = true := by
  decide +kernel

theorem ok190 : check start190 proof190 = true := by
  decide +kernel

theorem ok191 : check start191 proof191 = true := by
  decide +kernel

theorem ok192 : andB (check start192 proof192) (cpOk (replay start192 proof192) start193) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow143
