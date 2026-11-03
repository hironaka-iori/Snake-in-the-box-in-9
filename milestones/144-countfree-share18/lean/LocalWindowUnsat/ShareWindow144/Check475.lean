import LocalWindowUnsat.ShareWindow144.Data475
import LocalWindowUnsat.ShareWindow144.Data476

/-! Kernel checks of segments 1897-1900 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok1897 : check start1897 proof1897 = true := by
  decide +kernel

theorem ok1898 : check start1898 proof1898 = true := by
  decide +kernel

theorem ok1899 : check start1899 proof1899 = true := by
  decide +kernel

theorem ok1900 : andB (check start1900 proof1900) (cpOk (replay start1900 proof1900) start1901) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
