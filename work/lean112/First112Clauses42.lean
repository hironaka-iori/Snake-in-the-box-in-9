import First112Semantics
import Dfs112FirstBooleanInputs
namespace Snake9.Regrowth.First112
noncomputable section
local instance blockDec42 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause1345 (q : Snake 81) (h : Conditions q) : valuation q 1675 = false ∨ valuation q 1687 = true := by
  have hs : count1687 q = (countLit q [-92, -93, -95, -97]) + (countLit q [-98, -101, -104, -105]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-92, -93, -95, -97]) (l₂ := [-98, -101, -104, -105])
  have hm := merge_left (literal (valuation q) (1675)) (literal (valuation q) (1687)) (countLit q [-92, -93, -95, -97]) (countLit q [-98, -101, -104, -105]) (count1687 q) 1 (meaning1675 q) (meaning1687 q) hs
  change valuation q 1675 = false ∨ valuation q 1687 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1346 (q : Snake 81) (h : Conditions q) : valuation q 1675 = false ∨ valuation q 1683 = false ∨ valuation q 1688 = true := by
  have hs : count1687 q = (countLit q [-92, -93, -95, -97]) + (countLit q [-98, -101, -104, -105]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-92, -93, -95, -97]) (l₂ := [-98, -101, -104, -105])
  have hm := merge_two (literal (valuation q) (1675)) (literal (valuation q) (1683)) (literal (valuation q) (1688)) (countLit q [-92, -93, -95, -97]) (countLit q [-98, -101, -104, -105]) (count1687 q) 1 1 (meaning1675 q) (meaning1683 q) (meaning1688 q) hs
  change valuation q 1675 = false ∨ valuation q 1683 = false ∨ valuation q 1688 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1347 (q : Snake 81) (h : Conditions q) : valuation q 1675 = false ∨ valuation q 1684 = false ∨ valuation q 1689 = true := by
  have hs : count1687 q = (countLit q [-92, -93, -95, -97]) + (countLit q [-98, -101, -104, -105]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-92, -93, -95, -97]) (l₂ := [-98, -101, -104, -105])
  have hm := merge_two (literal (valuation q) (1675)) (literal (valuation q) (1684)) (literal (valuation q) (1689)) (countLit q [-92, -93, -95, -97]) (countLit q [-98, -101, -104, -105]) (count1687 q) 1 2 (meaning1675 q) (meaning1684 q) (meaning1689 q) hs
  change valuation q 1675 = false ∨ valuation q 1684 = false ∨ valuation q 1689 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1348 (q : Snake 81) (h : Conditions q) : valuation q 1675 = false ∨ valuation q 1685 = false ∨ valuation q 1690 = true := by
  have hs : count1687 q = (countLit q [-92, -93, -95, -97]) + (countLit q [-98, -101, -104, -105]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-92, -93, -95, -97]) (l₂ := [-98, -101, -104, -105])
  have hm := merge_two (literal (valuation q) (1675)) (literal (valuation q) (1685)) (literal (valuation q) (1690)) (countLit q [-92, -93, -95, -97]) (countLit q [-98, -101, -104, -105]) (count1687 q) 1 3 (meaning1675 q) (meaning1685 q) (meaning1690 q) hs
  change valuation q 1675 = false ∨ valuation q 1685 = false ∨ valuation q 1690 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1349 (q : Snake 81) (h : Conditions q) : valuation q 1675 = false ∨ valuation q 1686 = false ∨ valuation q 1691 = true := by
  have hs : count1687 q = (countLit q [-92, -93, -95, -97]) + (countLit q [-98, -101, -104, -105]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-92, -93, -95, -97]) (l₂ := [-98, -101, -104, -105])
  have hm := merge_two (literal (valuation q) (1675)) (literal (valuation q) (1686)) (literal (valuation q) (1691)) (countLit q [-92, -93, -95, -97]) (countLit q [-98, -101, -104, -105]) (count1687 q) 1 4 (meaning1675 q) (meaning1686 q) (meaning1691 q) hs
  change valuation q 1675 = false ∨ valuation q 1686 = false ∨ valuation q 1691 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1350 (q : Snake 81) (h : Conditions q) : valuation q 1676 = false ∨ valuation q 1688 = true := by
  have hs : count1687 q = (countLit q [-92, -93, -95, -97]) + (countLit q [-98, -101, -104, -105]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-92, -93, -95, -97]) (l₂ := [-98, -101, -104, -105])
  have hm := merge_left (literal (valuation q) (1676)) (literal (valuation q) (1688)) (countLit q [-92, -93, -95, -97]) (countLit q [-98, -101, -104, -105]) (count1687 q) 2 (meaning1676 q) (meaning1688 q) hs
  change valuation q 1676 = false ∨ valuation q 1688 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1351 (q : Snake 81) (h : Conditions q) : valuation q 1676 = false ∨ valuation q 1683 = false ∨ valuation q 1689 = true := by
  have hs : count1687 q = (countLit q [-92, -93, -95, -97]) + (countLit q [-98, -101, -104, -105]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-92, -93, -95, -97]) (l₂ := [-98, -101, -104, -105])
  have hm := merge_two (literal (valuation q) (1676)) (literal (valuation q) (1683)) (literal (valuation q) (1689)) (countLit q [-92, -93, -95, -97]) (countLit q [-98, -101, -104, -105]) (count1687 q) 2 1 (meaning1676 q) (meaning1683 q) (meaning1689 q) hs
  change valuation q 1676 = false ∨ valuation q 1683 = false ∨ valuation q 1689 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1352 (q : Snake 81) (h : Conditions q) : valuation q 1676 = false ∨ valuation q 1684 = false ∨ valuation q 1690 = true := by
  have hs : count1687 q = (countLit q [-92, -93, -95, -97]) + (countLit q [-98, -101, -104, -105]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-92, -93, -95, -97]) (l₂ := [-98, -101, -104, -105])
  have hm := merge_two (literal (valuation q) (1676)) (literal (valuation q) (1684)) (literal (valuation q) (1690)) (countLit q [-92, -93, -95, -97]) (countLit q [-98, -101, -104, -105]) (count1687 q) 2 2 (meaning1676 q) (meaning1684 q) (meaning1690 q) hs
  change valuation q 1676 = false ∨ valuation q 1684 = false ∨ valuation q 1690 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1353 (q : Snake 81) (h : Conditions q) : valuation q 1676 = false ∨ valuation q 1685 = false ∨ valuation q 1691 = true := by
  have hs : count1687 q = (countLit q [-92, -93, -95, -97]) + (countLit q [-98, -101, -104, -105]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-92, -93, -95, -97]) (l₂ := [-98, -101, -104, -105])
  have hm := merge_two (literal (valuation q) (1676)) (literal (valuation q) (1685)) (literal (valuation q) (1691)) (countLit q [-92, -93, -95, -97]) (countLit q [-98, -101, -104, -105]) (count1687 q) 2 3 (meaning1676 q) (meaning1685 q) (meaning1691 q) hs
  change valuation q 1676 = false ∨ valuation q 1685 = false ∨ valuation q 1691 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1354 (q : Snake 81) (h : Conditions q) : valuation q 1676 = false ∨ valuation q 1686 = false ∨ valuation q 1692 = true := by
  have hs : count1687 q = (countLit q [-92, -93, -95, -97]) + (countLit q [-98, -101, -104, -105]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-92, -93, -95, -97]) (l₂ := [-98, -101, -104, -105])
  have hm := merge_two (literal (valuation q) (1676)) (literal (valuation q) (1686)) (literal (valuation q) (1692)) (countLit q [-92, -93, -95, -97]) (countLit q [-98, -101, -104, -105]) (count1687 q) 2 4 (meaning1676 q) (meaning1686 q) (meaning1692 q) hs
  change valuation q 1676 = false ∨ valuation q 1686 = false ∨ valuation q 1692 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1355 (q : Snake 81) (h : Conditions q) : valuation q 1677 = false ∨ valuation q 1689 = true := by
  have hs : count1687 q = (countLit q [-92, -93, -95, -97]) + (countLit q [-98, -101, -104, -105]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-92, -93, -95, -97]) (l₂ := [-98, -101, -104, -105])
  have hm := merge_left (literal (valuation q) (1677)) (literal (valuation q) (1689)) (countLit q [-92, -93, -95, -97]) (countLit q [-98, -101, -104, -105]) (count1687 q) 3 (meaning1677 q) (meaning1689 q) hs
  change valuation q 1677 = false ∨ valuation q 1689 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1356 (q : Snake 81) (h : Conditions q) : valuation q 1677 = false ∨ valuation q 1683 = false ∨ valuation q 1690 = true := by
  have hs : count1687 q = (countLit q [-92, -93, -95, -97]) + (countLit q [-98, -101, -104, -105]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-92, -93, -95, -97]) (l₂ := [-98, -101, -104, -105])
  have hm := merge_two (literal (valuation q) (1677)) (literal (valuation q) (1683)) (literal (valuation q) (1690)) (countLit q [-92, -93, -95, -97]) (countLit q [-98, -101, -104, -105]) (count1687 q) 3 1 (meaning1677 q) (meaning1683 q) (meaning1690 q) hs
  change valuation q 1677 = false ∨ valuation q 1683 = false ∨ valuation q 1690 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1357 (q : Snake 81) (h : Conditions q) : valuation q 1677 = false ∨ valuation q 1684 = false ∨ valuation q 1691 = true := by
  have hs : count1687 q = (countLit q [-92, -93, -95, -97]) + (countLit q [-98, -101, -104, -105]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-92, -93, -95, -97]) (l₂ := [-98, -101, -104, -105])
  have hm := merge_two (literal (valuation q) (1677)) (literal (valuation q) (1684)) (literal (valuation q) (1691)) (countLit q [-92, -93, -95, -97]) (countLit q [-98, -101, -104, -105]) (count1687 q) 3 2 (meaning1677 q) (meaning1684 q) (meaning1691 q) hs
  change valuation q 1677 = false ∨ valuation q 1684 = false ∨ valuation q 1691 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1358 (q : Snake 81) (h : Conditions q) : valuation q 1677 = false ∨ valuation q 1685 = false ∨ valuation q 1692 = true := by
  have hs : count1687 q = (countLit q [-92, -93, -95, -97]) + (countLit q [-98, -101, -104, -105]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-92, -93, -95, -97]) (l₂ := [-98, -101, -104, -105])
  have hm := merge_two (literal (valuation q) (1677)) (literal (valuation q) (1685)) (literal (valuation q) (1692)) (countLit q [-92, -93, -95, -97]) (countLit q [-98, -101, -104, -105]) (count1687 q) 3 3 (meaning1677 q) (meaning1685 q) (meaning1692 q) hs
  change valuation q 1677 = false ∨ valuation q 1685 = false ∨ valuation q 1692 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1359 (q : Snake 81) (h : Conditions q) : valuation q 1677 = false ∨ valuation q 1686 = false ∨ valuation q 1693 = true := by
  have hs : count1687 q = (countLit q [-92, -93, -95, -97]) + (countLit q [-98, -101, -104, -105]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-92, -93, -95, -97]) (l₂ := [-98, -101, -104, -105])
  have hm := merge_two (literal (valuation q) (1677)) (literal (valuation q) (1686)) (literal (valuation q) (1693)) (countLit q [-92, -93, -95, -97]) (countLit q [-98, -101, -104, -105]) (count1687 q) 3 4 (meaning1677 q) (meaning1686 q) (meaning1693 q) hs
  change valuation q 1677 = false ∨ valuation q 1686 = false ∨ valuation q 1693 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1360 (q : Snake 81) (h : Conditions q) : valuation q 1678 = false ∨ valuation q 1690 = true := by
  have hs : count1687 q = (countLit q [-92, -93, -95, -97]) + (countLit q [-98, -101, -104, -105]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-92, -93, -95, -97]) (l₂ := [-98, -101, -104, -105])
  have hm := merge_left (literal (valuation q) (1678)) (literal (valuation q) (1690)) (countLit q [-92, -93, -95, -97]) (countLit q [-98, -101, -104, -105]) (count1687 q) 4 (meaning1678 q) (meaning1690 q) hs
  change valuation q 1678 = false ∨ valuation q 1690 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1361 (q : Snake 81) (h : Conditions q) : valuation q 1678 = false ∨ valuation q 1683 = false ∨ valuation q 1691 = true := by
  have hs : count1687 q = (countLit q [-92, -93, -95, -97]) + (countLit q [-98, -101, -104, -105]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-92, -93, -95, -97]) (l₂ := [-98, -101, -104, -105])
  have hm := merge_two (literal (valuation q) (1678)) (literal (valuation q) (1683)) (literal (valuation q) (1691)) (countLit q [-92, -93, -95, -97]) (countLit q [-98, -101, -104, -105]) (count1687 q) 4 1 (meaning1678 q) (meaning1683 q) (meaning1691 q) hs
  change valuation q 1678 = false ∨ valuation q 1683 = false ∨ valuation q 1691 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1362 (q : Snake 81) (h : Conditions q) : valuation q 1678 = false ∨ valuation q 1684 = false ∨ valuation q 1692 = true := by
  have hs : count1687 q = (countLit q [-92, -93, -95, -97]) + (countLit q [-98, -101, -104, -105]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-92, -93, -95, -97]) (l₂ := [-98, -101, -104, -105])
  have hm := merge_two (literal (valuation q) (1678)) (literal (valuation q) (1684)) (literal (valuation q) (1692)) (countLit q [-92, -93, -95, -97]) (countLit q [-98, -101, -104, -105]) (count1687 q) 4 2 (meaning1678 q) (meaning1684 q) (meaning1692 q) hs
  change valuation q 1678 = false ∨ valuation q 1684 = false ∨ valuation q 1692 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1363 (q : Snake 81) (h : Conditions q) : valuation q 1678 = false ∨ valuation q 1685 = false ∨ valuation q 1693 = true := by
  have hs : count1687 q = (countLit q [-92, -93, -95, -97]) + (countLit q [-98, -101, -104, -105]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-92, -93, -95, -97]) (l₂ := [-98, -101, -104, -105])
  have hm := merge_two (literal (valuation q) (1678)) (literal (valuation q) (1685)) (literal (valuation q) (1693)) (countLit q [-92, -93, -95, -97]) (countLit q [-98, -101, -104, -105]) (count1687 q) 4 3 (meaning1678 q) (meaning1685 q) (meaning1693 q) hs
  change valuation q 1678 = false ∨ valuation q 1685 = false ∨ valuation q 1693 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1364 (q : Snake 81) (h : Conditions q) : valuation q 110 = true ∨ valuation q 1695 = true := by
  have hs : count1695 q = (countLit q [-109]) + (countLit q [-110]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-109]) (l₂ := [-110])
  have hm := merge_right (literal (valuation q) (-110)) (literal (valuation q) (1695)) (countLit q [-109]) (countLit q [-110]) (count1695 q) 1 (meaningNeg110 q) (meaning1695 q) hs
  change (! (valuation q 110)) = false ∨ valuation q 1695 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1365 (q : Snake 81) (h : Conditions q) : valuation q 109 = true ∨ valuation q 1695 = true := by
  have hs : count1695 q = (countLit q [-109]) + (countLit q [-110]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-109]) (l₂ := [-110])
  have hm := merge_left (literal (valuation q) (-109)) (literal (valuation q) (1695)) (countLit q [-109]) (countLit q [-110]) (count1695 q) 1 (meaningNeg109 q) (meaning1695 q) hs
  change (! (valuation q 109)) = false ∨ valuation q 1695 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1366 (q : Snake 81) (h : Conditions q) : valuation q 109 = true ∨ valuation q 110 = true ∨ valuation q 1696 = true := by
  have hs : count1695 q = (countLit q [-109]) + (countLit q [-110]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-109]) (l₂ := [-110])
  have hm := merge_two (literal (valuation q) (-109)) (literal (valuation q) (-110)) (literal (valuation q) (1696)) (countLit q [-109]) (countLit q [-110]) (count1695 q) 1 1 (meaningNeg109 q) (meaningNeg110 q) (meaning1696 q) hs
  change (! (valuation q 109)) = false ∨ (! (valuation q 110)) = false ∨ valuation q 1696 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1367 (q : Snake 81) (h : Conditions q) : valuation q 113 = true ∨ valuation q 1697 = true := by
  have hs : count1697 q = (countLit q [-111]) + (countLit q [-113]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-111]) (l₂ := [-113])
  have hm := merge_right (literal (valuation q) (-113)) (literal (valuation q) (1697)) (countLit q [-111]) (countLit q [-113]) (count1697 q) 1 (meaningNeg113 q) (meaning1697 q) hs
  change (! (valuation q 113)) = false ∨ valuation q 1697 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1368 (q : Snake 81) (h : Conditions q) : valuation q 111 = true ∨ valuation q 1697 = true := by
  have hs : count1697 q = (countLit q [-111]) + (countLit q [-113]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-111]) (l₂ := [-113])
  have hm := merge_left (literal (valuation q) (-111)) (literal (valuation q) (1697)) (countLit q [-111]) (countLit q [-113]) (count1697 q) 1 (meaningNeg111 q) (meaning1697 q) hs
  change (! (valuation q 111)) = false ∨ valuation q 1697 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1369 (q : Snake 81) (h : Conditions q) : valuation q 111 = true ∨ valuation q 113 = true ∨ valuation q 1698 = true := by
  have hs : count1697 q = (countLit q [-111]) + (countLit q [-113]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-111]) (l₂ := [-113])
  have hm := merge_two (literal (valuation q) (-111)) (literal (valuation q) (-113)) (literal (valuation q) (1698)) (countLit q [-111]) (countLit q [-113]) (count1697 q) 1 1 (meaningNeg111 q) (meaningNeg113 q) (meaning1698 q) hs
  change (! (valuation q 111)) = false ∨ (! (valuation q 113)) = false ∨ valuation q 1698 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1370 (q : Snake 81) (h : Conditions q) : valuation q 1697 = false ∨ valuation q 1699 = true := by
  have hs : count1699 q = (countLit q [-109, -110]) + (countLit q [-111, -113]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-109, -110]) (l₂ := [-111, -113])
  have hm := merge_right (literal (valuation q) (1697)) (literal (valuation q) (1699)) (countLit q [-109, -110]) (countLit q [-111, -113]) (count1699 q) 1 (meaning1697 q) (meaning1699 q) hs
  change valuation q 1697 = false ∨ valuation q 1699 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1371 (q : Snake 81) (h : Conditions q) : valuation q 1698 = false ∨ valuation q 1700 = true := by
  have hs : count1699 q = (countLit q [-109, -110]) + (countLit q [-111, -113]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-109, -110]) (l₂ := [-111, -113])
  have hm := merge_right (literal (valuation q) (1698)) (literal (valuation q) (1700)) (countLit q [-109, -110]) (countLit q [-111, -113]) (count1699 q) 2 (meaning1698 q) (meaning1700 q) hs
  change valuation q 1698 = false ∨ valuation q 1700 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1372 (q : Snake 81) (h : Conditions q) : valuation q 1695 = false ∨ valuation q 1699 = true := by
  have hs : count1699 q = (countLit q [-109, -110]) + (countLit q [-111, -113]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-109, -110]) (l₂ := [-111, -113])
  have hm := merge_left (literal (valuation q) (1695)) (literal (valuation q) (1699)) (countLit q [-109, -110]) (countLit q [-111, -113]) (count1699 q) 1 (meaning1695 q) (meaning1699 q) hs
  change valuation q 1695 = false ∨ valuation q 1699 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1373 (q : Snake 81) (h : Conditions q) : valuation q 1695 = false ∨ valuation q 1697 = false ∨ valuation q 1700 = true := by
  have hs : count1699 q = (countLit q [-109, -110]) + (countLit q [-111, -113]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-109, -110]) (l₂ := [-111, -113])
  have hm := merge_two (literal (valuation q) (1695)) (literal (valuation q) (1697)) (literal (valuation q) (1700)) (countLit q [-109, -110]) (countLit q [-111, -113]) (count1699 q) 1 1 (meaning1695 q) (meaning1697 q) (meaning1700 q) hs
  change valuation q 1695 = false ∨ valuation q 1697 = false ∨ valuation q 1700 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1374 (q : Snake 81) (h : Conditions q) : valuation q 1695 = false ∨ valuation q 1698 = false ∨ valuation q 1701 = true := by
  have hs : count1699 q = (countLit q [-109, -110]) + (countLit q [-111, -113]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-109, -110]) (l₂ := [-111, -113])
  have hm := merge_two (literal (valuation q) (1695)) (literal (valuation q) (1698)) (literal (valuation q) (1701)) (countLit q [-109, -110]) (countLit q [-111, -113]) (count1699 q) 1 2 (meaning1695 q) (meaning1698 q) (meaning1701 q) hs
  change valuation q 1695 = false ∨ valuation q 1698 = false ∨ valuation q 1701 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1375 (q : Snake 81) (h : Conditions q) : valuation q 1696 = false ∨ valuation q 1700 = true := by
  have hs : count1699 q = (countLit q [-109, -110]) + (countLit q [-111, -113]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-109, -110]) (l₂ := [-111, -113])
  have hm := merge_left (literal (valuation q) (1696)) (literal (valuation q) (1700)) (countLit q [-109, -110]) (countLit q [-111, -113]) (count1699 q) 2 (meaning1696 q) (meaning1700 q) hs
  change valuation q 1696 = false ∨ valuation q 1700 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1376 (q : Snake 81) (h : Conditions q) : valuation q 1696 = false ∨ valuation q 1697 = false ∨ valuation q 1701 = true := by
  have hs : count1699 q = (countLit q [-109, -110]) + (countLit q [-111, -113]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-109, -110]) (l₂ := [-111, -113])
  have hm := merge_two (literal (valuation q) (1696)) (literal (valuation q) (1697)) (literal (valuation q) (1701)) (countLit q [-109, -110]) (countLit q [-111, -113]) (count1699 q) 2 1 (meaning1696 q) (meaning1697 q) (meaning1701 q) hs
  change valuation q 1696 = false ∨ valuation q 1697 = false ∨ valuation q 1701 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem block42 (q : Snake 81) (h : Conditions q) : Dfs112FirstBoolean.Block42 (valuation q) :=
  ⟨clause1345 q h, clause1346 q h, clause1347 q h, clause1348 q h, clause1349 q h, clause1350 q h, clause1351 q h, clause1352 q h, clause1353 q h, clause1354 q h, clause1355 q h, clause1356 q h, clause1357 q h, clause1358 q h, clause1359 q h, clause1360 q h, clause1361 q h, clause1362 q h, clause1363 q h, clause1364 q h, clause1365 q h, clause1366 q h, clause1367 q h, clause1368 q h, clause1369 q h, clause1370 q h, clause1371 q h, clause1372 q h, clause1373 q h, clause1374 q h, clause1375 q h, clause1376 q h⟩

end
end Snake9.Regrowth.First112
