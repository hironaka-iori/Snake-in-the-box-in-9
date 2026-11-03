import LocalWindowUnsat.ShareWindow144.Data454
import LocalWindowUnsat.ShareWindow144.Data455

/-! Kernel checks of segments 1813-1816 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok1813 : check start1813 proof1813 = true := by
  decide +kernel

theorem ok1814 : check start1814 proof1814 = true := by
  decide +kernel

theorem ok1815 : check start1815 proof1815 = true := by
  decide +kernel

theorem ok1816 : andB (check start1816 proof1816) (cpOk (replay start1816 proof1816) start1817) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
