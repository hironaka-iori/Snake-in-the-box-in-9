import LocalWindowSat.ShareObstruction530.Data
import ShareCheckAppend
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Snake9.LocalWindow.ShareObstruction530
open Snake9.LocalWindow.Tags
theorem counters_checked : ctrs.all (ctrOK meaning (centresK window bounds)) = true := by decide +kernel
end Snake9.LocalWindow.ShareObstruction530
