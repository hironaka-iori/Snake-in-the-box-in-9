import DirectionTables
import PrunedEnumeration
namespace Snake9.Direction77
open Snake9.WindowAutomaton
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem tail_8_4 : allPruned 1 6 [0, 1, 2, 3, 4, 5, 4]
    (fun c => shapes.contains c) = true := by decide +kernel
#print axioms tail_8_4
theorem tail_9_4 : allPruned 2 6 [0, 1, 2, 3, 4, 5, 4]
    (fun c => extensions.contains c) = true := by decide +kernel
#print axioms tail_9_4
end Snake9.Direction77
