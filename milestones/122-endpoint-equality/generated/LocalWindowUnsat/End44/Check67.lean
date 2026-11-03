import LocalWindowUnsat.End44.Data67
import LocalWindowUnsat.End44.Data68

/-! Kernel checks of segments 397-402 of `end44` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.End44
open Snake9.LratFastEndpoint122
open Snake9.Lrat (Tree TreeTrue andB)

theorem ok397 : check start397 proof397 = true := by
  decide +kernel

theorem ok398 : check start398 proof398 = true := by
  decide +kernel

theorem ok399 : check start399 proof399 = true := by
  decide +kernel

theorem ok400 : check start400 proof400 = true := by
  decide +kernel

theorem ok401 : check start401 proof401 = true := by
  decide +kernel

theorem ok402 : andB (check start402 proof402) (cpOk (replay start402 proof402) start403) = true := by
  decide +kernel

end Snake9.LocalWindow.End44
