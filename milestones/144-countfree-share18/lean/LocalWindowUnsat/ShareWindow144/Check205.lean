import LocalWindowUnsat.ShareWindow144.Data205
import LocalWindowUnsat.ShareWindow144.Data206

/-! Kernel checks of segments 817-820 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok817 : check start817 proof817 = true := by
  decide +kernel

theorem ok818 : check start818 proof818 = true := by
  decide +kernel

theorem ok819 : check start819 proof819 = true := by
  decide +kernel

theorem ok820 : andB (check start820 proof820) (cpOk (replay start820 proof820) start821) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
