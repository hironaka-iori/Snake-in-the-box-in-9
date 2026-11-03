import Recovered122G.LocalWindowUnsat.End44.Data102
import Recovered122G.LocalWindowUnsat.End44.Data103

/-! Kernel checks of segments 607-612 of `end44` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.End44
open Snake9.LratFastEndpoint122
open Snake9.Lrat (Tree TreeTrue andB)

theorem ok607 : check start607 proof607 = true := by
  decide +kernel

theorem ok608 : check start608 proof608 = true := by
  decide +kernel

theorem ok609 : check start609 proof609 = true := by
  decide +kernel

theorem ok610 : check start610 proof610 = true := by
  decide +kernel

theorem ok611 : check start611 proof611 = true := by
  decide +kernel

theorem ok612 : andB (check start612 proof612) (cpOk (replay start612 proof612) start613) = true := by
  decide +kernel

end Snake9.LocalWindow.End44
