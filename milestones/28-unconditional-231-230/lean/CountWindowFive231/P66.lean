import CountWindowFive231.Data
set_option maxHeartbeats 0
set_option maxRecDepth 200000

namespace Snake9.CountWindowFive231
open LocalWindow DirectionWindow WindowAutomaton CountWindowBridge
open CountWindowTable231 CountWindowTablePrefix231

theorem prefix66 : prefixCovered keys 6 [6,6] = true := by decide +kernel
end Snake9.CountWindowFive231
