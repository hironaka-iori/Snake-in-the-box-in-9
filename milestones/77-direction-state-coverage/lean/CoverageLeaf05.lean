import DirectionTables
import PrunedEnumeration
namespace Snake9.Direction77
open Snake9.WindowAutomaton
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem leaf_8_5 : allPruned 2 5 [0, 1, 2, 3, 0, 4]
    (fun c => shapes.contains c) = true := by decide +kernel
#print axioms leaf_8_5
theorem leaf_9_5 : allPruned 3 5 [0, 1, 2, 3, 0, 4]
    (fun c => extensions.contains c) = true := by decide +kernel
#print axioms leaf_9_5
end Snake9.Direction77
