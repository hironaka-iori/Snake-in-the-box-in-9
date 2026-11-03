import LocalWindowUnsat.ShareWindow144.Data472
import LocalWindowUnsat.ShareWindow144.Data473

/-! Kernel checks of segments 1885-1888 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok1885 : check start1885 proof1885 = true := by
  decide +kernel

theorem ok1886 : check start1886 proof1886 = true := by
  decide +kernel

theorem ok1887 : check start1887 proof1887 = true := by
  decide +kernel

theorem ok1888 : andB (check start1888 proof1888) (cpOk (replay start1888 proof1888) start1889) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
