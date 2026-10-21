import CountWindowSix231.Data
set_option maxHeartbeats 0
set_option maxRecDepth 200000

namespace Snake9.CountWindowSix231
open LocalWindow DirectionWindow WindowAutomaton CountWindowBridge
open CountWindowTable231 CountWindowTablePrefix231

theorem prefix57 : prefixCovered keys 7 [5,7] = true := by decide +kernel
end Snake9.CountWindowSix231
