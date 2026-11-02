import PrunedAssembly
import CoverageLeaf00
import CoverageLeaf01
import CoverageLeaf02
import CoverageLeaf03
import CoverageLeaf04
import CoverageLeaf05
import CoverageLeaf06
import CoverageLeaf07
import CoverageLeaf08
import CoverageLeaf09
import CoverageLeaf10
import CoverageLeaf11
namespace Snake9.Direction77
open Snake9.WindowAutomaton
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem coverage_8_00 : allPruned 6 1 [0, 0]
    (fun c => shapes.contains c) = true := by
  decide +kernel
theorem coverage_8_010 : allPruned 5 2 [0, 1, 0]
    (fun c => shapes.contains c) = true := by
  decide +kernel
theorem coverage_8_011 : allPruned 5 2 [0, 1, 1]
    (fun c => shapes.contains c) = true := by
  decide +kernel
theorem coverage_8_01200 : allPruned 3 3 [0, 1, 2, 0, 0]
    (fun c => shapes.contains c) = true := by
  decide +kernel
theorem coverage_8_01201 : allPruned 3 3 [0, 1, 2, 0, 1]
    (fun c => shapes.contains c) = true := by
  decide +kernel
theorem coverage_8_01202 : allPruned 3 3 [0, 1, 2, 0, 2]
    (fun c => shapes.contains c) = true := by
  decide +kernel
theorem coverage_8_012030 : allPruned 2 4 [0, 1, 2, 0, 3, 0]
    (fun c => shapes.contains c) = true := by
  decide +kernel
theorem coverage_8_012033 : allPruned 2 4 [0, 1, 2, 0, 3, 3]
    (fun c => shapes.contains c) = true := by
  decide +kernel
theorem coverage_8_01203 : allPruned 3 4 [0, 1, 2, 0, 3]
    (fun c => shapes.contains c) = true := by
  apply allPruned_step
  intro a ha
  interval_cases a
  · exact coverage_8_012030
  · exact leaf_8_0
  · exact leaf_8_1
  · exact coverage_8_012033
  · exact leaf_8_2
theorem coverage_8_0120 : allPruned 4 3 [0, 1, 2, 0]
    (fun c => shapes.contains c) = true := by
  apply allPruned_step
  intro a ha
  interval_cases a
  · exact coverage_8_01200
  · exact coverage_8_01201
  · exact coverage_8_01202
  · exact coverage_8_01203
theorem coverage_8_0121 : allPruned 4 3 [0, 1, 2, 1]
    (fun c => shapes.contains c) = true := by
  decide +kernel
theorem coverage_8_0122 : allPruned 4 3 [0, 1, 2, 2]
    (fun c => shapes.contains c) = true := by
  decide +kernel
theorem coverage_8_012300 : allPruned 2 4 [0, 1, 2, 3, 0, 0]
    (fun c => shapes.contains c) = true := by
  decide +kernel
theorem coverage_8_012303 : allPruned 2 4 [0, 1, 2, 3, 0, 3]
    (fun c => shapes.contains c) = true := by
  decide +kernel
theorem coverage_8_01230 : allPruned 3 4 [0, 1, 2, 3, 0]
    (fun c => shapes.contains c) = true := by
  apply allPruned_step
  intro a ha
  interval_cases a
  · exact coverage_8_012300
  · exact leaf_8_3
  · exact leaf_8_4
  · exact coverage_8_012303
  · exact leaf_8_5
theorem coverage_8_012311 : allPruned 2 4 [0, 1, 2, 3, 1, 1]
    (fun c => shapes.contains c) = true := by
  decide +kernel
theorem coverage_8_012312 : allPruned 2 4 [0, 1, 2, 3, 1, 2]
    (fun c => shapes.contains c) = true := by
  decide +kernel
theorem coverage_8_012313 : allPruned 2 4 [0, 1, 2, 3, 1, 3]
    (fun c => shapes.contains c) = true := by
  decide +kernel
theorem coverage_8_01231 : allPruned 3 4 [0, 1, 2, 3, 1]
    (fun c => shapes.contains c) = true := by
  apply allPruned_step
  intro a ha
  interval_cases a
  · exact leaf_8_6
  · exact coverage_8_012311
  · exact coverage_8_012312
  · exact coverage_8_012313
  · exact leaf_8_7
theorem coverage_8_01232 : allPruned 3 4 [0, 1, 2, 3, 2]
    (fun c => shapes.contains c) = true := by
  decide +kernel
theorem coverage_8_01233 : allPruned 3 4 [0, 1, 2, 3, 3]
    (fun c => shapes.contains c) = true := by
  decide +kernel
theorem coverage_8_012343 : allPruned 2 5 [0, 1, 2, 3, 4, 3]
    (fun c => shapes.contains c) = true := by
  decide +kernel
theorem coverage_8_012344 : allPruned 2 5 [0, 1, 2, 3, 4, 4]
    (fun c => shapes.contains c) = true := by
  decide +kernel
theorem coverage_8_01234 : allPruned 3 5 [0, 1, 2, 3, 4]
    (fun c => shapes.contains c) = true := by
  apply allPruned_step
  intro a ha
  interval_cases a
  · exact leaf_8_8
  · exact leaf_8_9
  · exact leaf_8_10
  · exact coverage_8_012343
  · exact coverage_8_012344
  · exact leaf_8_11
theorem coverage_8_0123 : allPruned 4 4 [0, 1, 2, 3]
    (fun c => shapes.contains c) = true := by
  apply allPruned_step
  intro a ha
  interval_cases a
  · exact coverage_8_01230
  · exact coverage_8_01231
  · exact coverage_8_01232
  · exact coverage_8_01233
  · exact coverage_8_01234
theorem coverage_8_012 : allPruned 5 3 [0, 1, 2]
    (fun c => shapes.contains c) = true := by
  apply allPruned_step
  intro a ha
  interval_cases a
  · exact coverage_8_0120
  · exact coverage_8_0121
  · exact coverage_8_0122
  · exact coverage_8_0123
theorem coverage_8_01 : allPruned 6 2 [0, 1]
    (fun c => shapes.contains c) = true := by
  apply allPruned_step
  intro a ha
  interval_cases a
  · exact coverage_8_010
  · exact coverage_8_011
  · exact coverage_8_012
theorem coverage_8_0 : allPruned 7 1 [0]
    (fun c => shapes.contains c) = true := by
  apply allPruned_step
  intro a ha
  interval_cases a
  · exact coverage_8_00
  · exact coverage_8_01
theorem coverage_8_root : allPruned 8 0 []
    (fun c => shapes.contains c) = true := by
  apply allPruned_step
  intro a ha
  interval_cases a
  · exact coverage_8_0
#print axioms coverage_8_root
theorem coverage_9_00 : allPruned 7 1 [0, 0]
    (fun c => extensions.contains c) = true := by
  decide +kernel
theorem coverage_9_010 : allPruned 6 2 [0, 1, 0]
    (fun c => extensions.contains c) = true := by
  decide +kernel
theorem coverage_9_011 : allPruned 6 2 [0, 1, 1]
    (fun c => extensions.contains c) = true := by
  decide +kernel
theorem coverage_9_01200 : allPruned 4 3 [0, 1, 2, 0, 0]
    (fun c => extensions.contains c) = true := by
  decide +kernel
theorem coverage_9_01201 : allPruned 4 3 [0, 1, 2, 0, 1]
    (fun c => extensions.contains c) = true := by
  decide +kernel
theorem coverage_9_01202 : allPruned 4 3 [0, 1, 2, 0, 2]
    (fun c => extensions.contains c) = true := by
  decide +kernel
theorem coverage_9_012030 : allPruned 3 4 [0, 1, 2, 0, 3, 0]
    (fun c => extensions.contains c) = true := by
  decide +kernel
theorem coverage_9_012033 : allPruned 3 4 [0, 1, 2, 0, 3, 3]
    (fun c => extensions.contains c) = true := by
  decide +kernel
theorem coverage_9_01203 : allPruned 4 4 [0, 1, 2, 0, 3]
    (fun c => extensions.contains c) = true := by
  apply allPruned_step
  intro a ha
  interval_cases a
  · exact coverage_9_012030
  · exact leaf_9_0
  · exact leaf_9_1
  · exact coverage_9_012033
  · exact leaf_9_2
theorem coverage_9_0120 : allPruned 5 3 [0, 1, 2, 0]
    (fun c => extensions.contains c) = true := by
  apply allPruned_step
  intro a ha
  interval_cases a
  · exact coverage_9_01200
  · exact coverage_9_01201
  · exact coverage_9_01202
  · exact coverage_9_01203
theorem coverage_9_0121 : allPruned 5 3 [0, 1, 2, 1]
    (fun c => extensions.contains c) = true := by
  decide +kernel
theorem coverage_9_0122 : allPruned 5 3 [0, 1, 2, 2]
    (fun c => extensions.contains c) = true := by
  decide +kernel
theorem coverage_9_012300 : allPruned 3 4 [0, 1, 2, 3, 0, 0]
    (fun c => extensions.contains c) = true := by
  decide +kernel
theorem coverage_9_012303 : allPruned 3 4 [0, 1, 2, 3, 0, 3]
    (fun c => extensions.contains c) = true := by
  decide +kernel
theorem coverage_9_01230 : allPruned 4 4 [0, 1, 2, 3, 0]
    (fun c => extensions.contains c) = true := by
  apply allPruned_step
  intro a ha
  interval_cases a
  · exact coverage_9_012300
  · exact leaf_9_3
  · exact leaf_9_4
  · exact coverage_9_012303
  · exact leaf_9_5
theorem coverage_9_012311 : allPruned 3 4 [0, 1, 2, 3, 1, 1]
    (fun c => extensions.contains c) = true := by
  decide +kernel
theorem coverage_9_012312 : allPruned 3 4 [0, 1, 2, 3, 1, 2]
    (fun c => extensions.contains c) = true := by
  decide +kernel
theorem coverage_9_012313 : allPruned 3 4 [0, 1, 2, 3, 1, 3]
    (fun c => extensions.contains c) = true := by
  decide +kernel
theorem coverage_9_01231 : allPruned 4 4 [0, 1, 2, 3, 1]
    (fun c => extensions.contains c) = true := by
  apply allPruned_step
  intro a ha
  interval_cases a
  · exact leaf_9_6
  · exact coverage_9_012311
  · exact coverage_9_012312
  · exact coverage_9_012313
  · exact leaf_9_7
theorem coverage_9_01232 : allPruned 4 4 [0, 1, 2, 3, 2]
    (fun c => extensions.contains c) = true := by
  decide +kernel
theorem coverage_9_01233 : allPruned 4 4 [0, 1, 2, 3, 3]
    (fun c => extensions.contains c) = true := by
  decide +kernel
theorem coverage_9_012343 : allPruned 3 5 [0, 1, 2, 3, 4, 3]
    (fun c => extensions.contains c) = true := by
  decide +kernel
theorem coverage_9_012344 : allPruned 3 5 [0, 1, 2, 3, 4, 4]
    (fun c => extensions.contains c) = true := by
  decide +kernel
theorem coverage_9_01234 : allPruned 4 5 [0, 1, 2, 3, 4]
    (fun c => extensions.contains c) = true := by
  apply allPruned_step
  intro a ha
  interval_cases a
  · exact leaf_9_8
  · exact leaf_9_9
  · exact leaf_9_10
  · exact coverage_9_012343
  · exact coverage_9_012344
  · exact leaf_9_11
theorem coverage_9_0123 : allPruned 5 4 [0, 1, 2, 3]
    (fun c => extensions.contains c) = true := by
  apply allPruned_step
  intro a ha
  interval_cases a
  · exact coverage_9_01230
  · exact coverage_9_01231
  · exact coverage_9_01232
  · exact coverage_9_01233
  · exact coverage_9_01234
theorem coverage_9_012 : allPruned 6 3 [0, 1, 2]
    (fun c => extensions.contains c) = true := by
  apply allPruned_step
  intro a ha
  interval_cases a
  · exact coverage_9_0120
  · exact coverage_9_0121
  · exact coverage_9_0122
  · exact coverage_9_0123
theorem coverage_9_01 : allPruned 7 2 [0, 1]
    (fun c => extensions.contains c) = true := by
  apply allPruned_step
  intro a ha
  interval_cases a
  · exact coverage_9_010
  · exact coverage_9_011
  · exact coverage_9_012
theorem coverage_9_0 : allPruned 8 1 [0]
    (fun c => extensions.contains c) = true := by
  apply allPruned_step
  intro a ha
  interval_cases a
  · exact coverage_9_00
  · exact coverage_9_01
theorem coverage_9_root : allPruned 9 0 []
    (fun c => extensions.contains c) = true := by
  apply allPruned_step
  intro a ha
  interval_cases a
  · exact coverage_9_0
#print axioms coverage_9_root
end Snake9.Direction77
