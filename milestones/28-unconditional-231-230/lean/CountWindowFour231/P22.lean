import CountWindowFour231.Data
set_option maxHeartbeats 0
set_option maxRecDepth 200000

namespace Snake9.CountWindowFour231
open LocalWindow DirectionWindow WindowAutomaton CountWindowBridge
open CountWindowTable231 CountWindowTablePrefix231

theorem prefix22 : prefixCovered keys 5 [2,2] = true := by decide +kernel
end Snake9.CountWindowFour231
