import DirectionTables
import PrunedEnumeration
namespace Snake9.Direction77
open Snake9.WindowAutomaton
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem leaf_8_3 : allPruned 2 4 [0, 1, 2, 3, 0, 1]
    (fun c => shapes.contains c) = true := by decide +kernel
#print axioms leaf_8_3
theorem leaf_9_3 : allPruned 3 4 [0, 1, 2, 3, 0, 1]
    (fun c => extensions.contains c) = true := by decide +kernel
#print axioms leaf_9_3
end Snake9.Direction77
