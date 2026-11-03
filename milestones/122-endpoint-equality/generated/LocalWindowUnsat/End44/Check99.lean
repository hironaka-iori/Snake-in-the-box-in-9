import LocalWindowUnsat.End44.Data99
import LocalWindowUnsat.End44.Data100

/-! Kernel checks of segments 589-594 of `end44` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.End44
open Snake9.LratFastEndpoint122
open Snake9.Lrat (Tree TreeTrue andB)

theorem ok589 : check start589 proof589 = true := by
  decide +kernel

theorem ok590 : check start590 proof590 = true := by
  decide +kernel

theorem ok591 : check start591 proof591 = true := by
  decide +kernel

theorem ok592 : check start592 proof592 = true := by
  decide +kernel

theorem ok593 : check start593 proof593 = true := by
  decide +kernel

theorem ok594 : andB (check start594 proof594) (cpOk (replay start594 proof594) start595) = true := by
  decide +kernel

end Snake9.LocalWindow.End44
