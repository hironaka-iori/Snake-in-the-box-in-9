import LocalWindowUnsat.End44.Data40
import LocalWindowUnsat.End44.Data41

/-! Kernel checks of segments 235-240 of `end44` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.End44
open Snake9.LratFastEndpoint122
open Snake9.Lrat (Tree TreeTrue andB)

theorem ok235 : check start235 proof235 = true := by
  decide +kernel

theorem ok236 : check start236 proof236 = true := by
  decide +kernel

theorem ok237 : check start237 proof237 = true := by
  decide +kernel

theorem ok238 : check start238 proof238 = true := by
  decide +kernel

theorem ok239 : check start239 proof239 = true := by
  decide +kernel

theorem ok240 : andB (check start240 proof240) (cpOk (replay start240 proof240) start241) = true := by
  decide +kernel

end Snake9.LocalWindow.End44
