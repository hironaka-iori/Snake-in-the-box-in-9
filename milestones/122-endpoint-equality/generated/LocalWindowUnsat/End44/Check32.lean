import LocalWindowUnsat.End44.Data32
import LocalWindowUnsat.End44.Data33

/-! Kernel checks of segments 187-192 of `end44` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.End44
open Snake9.LratFastEndpoint122
open Snake9.Lrat (Tree TreeTrue andB)

theorem ok187 : check start187 proof187 = true := by
  decide +kernel

theorem ok188 : check start188 proof188 = true := by
  decide +kernel

theorem ok189 : check start189 proof189 = true := by
  decide +kernel

theorem ok190 : check start190 proof190 = true := by
  decide +kernel

theorem ok191 : check start191 proof191 = true := by
  decide +kernel

theorem ok192 : andB (check start192 proof192) (cpOk (replay start192 proof192) start193) = true := by
  decide +kernel

end Snake9.LocalWindow.End44
