import PrunedAssembly
import CoverageTail00
import CoverageTail01
import CoverageTail02
import CoverageTail03
import CoverageTail04
import CoverageTail05
import CoverageTail06
namespace Snake9.Direction77
open Snake9.WindowAutomaton
theorem leaf_8_11 : allPruned 2 6 [0, 1, 2, 3, 4, 5]
    (fun c => shapes.contains c) = true := by
  apply allPruned_step
  intro a ha
  interval_cases a
  · exact tail_8_0
  · exact tail_8_1
  · exact tail_8_2
  · exact tail_8_3
  · exact tail_8_4
  · exact tail_8_5
  · exact tail_8_6
#print axioms leaf_8_11
theorem leaf_9_11 : allPruned 3 6 [0, 1, 2, 3, 4, 5]
    (fun c => extensions.contains c) = true := by
  apply allPruned_step
  intro a ha
  interval_cases a
  · exact tail_9_0
  · exact tail_9_1
  · exact tail_9_2
  · exact tail_9_3
  · exact tail_9_4
  · exact tail_9_5
  · exact tail_9_6
#print axioms leaf_9_11
end Snake9.Direction77
