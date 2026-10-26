import LocalWindowUnsat.ShareObstruction530.Data36
import LocalWindowUnsat.ShareObstruction530.Data37
import LocalWindowUnsat.ShareObstruction530.Data38
import LocalWindowUnsat.ShareObstruction530.Data39
import LocalWindowUnsat.ShareObstruction530.Data40
import LocalWindowUnsat.ShareObstruction530.Data41
import LocalWindowUnsat.ShareObstruction530.Data42

/-! Kernel checks of segments 37-42 of `obstruction0_95` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareObstruction530
open Snake9.LratFastO8k14
open Snake9.LratO8k (Tree TreeTrue andB)

theorem ok37 : check start37 proof37 = true := by
  decide +kernel

theorem ok38 : check start38 proof38 = true := by
  decide +kernel

theorem ok39 : check start39 proof39 = true := by
  decide +kernel

theorem ok40 : andB (check start40 proof40) (cpOk (replay start40 proof40) start41) = true := by
  decide +kernel

theorem ok41 : check start41 proof41 = true := by
  decide +kernel

theorem ok42 : andB (check start42 proof42) (hasEmpty (replay start42 proof42) 8192) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareObstruction530
