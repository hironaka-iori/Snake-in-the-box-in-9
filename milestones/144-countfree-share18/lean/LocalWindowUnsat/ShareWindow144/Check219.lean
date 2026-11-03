import LocalWindowUnsat.ShareWindow144.Data219
import LocalWindowUnsat.ShareWindow144.Data220

/-! Kernel checks of segments 873-876 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok873 : check start873 proof873 = true := by
  decide +kernel

theorem ok874 : check start874 proof874 = true := by
  decide +kernel

theorem ok875 : check start875 proof875 = true := by
  decide +kernel

theorem ok876 : andB (check start876 proof876) (cpOk (replay start876 proof876) start877) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
