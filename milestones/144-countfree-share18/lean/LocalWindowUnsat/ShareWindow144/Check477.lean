import LocalWindowUnsat.ShareWindow144.Data477
import LocalWindowUnsat.ShareWindow144.Data478

/-! Kernel checks of segments 1905-1908 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok1905 : check start1905 proof1905 = true := by
  decide +kernel

theorem ok1906 : check start1906 proof1906 = true := by
  decide +kernel

theorem ok1907 : check start1907 proof1907 = true := by
  decide +kernel

theorem ok1908 : andB (check start1908 proof1908) (cpOk (replay start1908 proof1908) start1909) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
