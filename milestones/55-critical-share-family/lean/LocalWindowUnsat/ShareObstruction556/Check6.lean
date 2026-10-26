import LocalWindowUnsat.ShareObstruction556.Data30
import LocalWindowUnsat.ShareObstruction556.Data31
import LocalWindowUnsat.ShareObstruction556.Data32
import LocalWindowUnsat.ShareObstruction556.Data33
import LocalWindowUnsat.ShareObstruction556.Data34
import LocalWindowUnsat.ShareObstruction556.Data35
import LocalWindowUnsat.ShareObstruction556.Data36

/-! Kernel checks of segments 31-36 of `obstruction6_95` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareObstruction556
open Snake9.LratFastO8k14
open Snake9.LratO8k (Tree TreeTrue andB)

theorem ok31 : check start31 proof31 = true := by
  decide +kernel

theorem ok32 : andB (check start32 proof32) (cpOk (replay start32 proof32) start33) = true := by
  decide +kernel

theorem ok33 : check start33 proof33 = true := by
  decide +kernel

theorem ok34 : check start34 proof34 = true := by
  decide +kernel

theorem ok35 : check start35 proof35 = true := by
  decide +kernel

theorem ok36 : andB (check start36 proof36) (hasEmpty (replay start36 proof36) 8192) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareObstruction556
