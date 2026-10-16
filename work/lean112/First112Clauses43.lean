import First112Semantics
import Dfs112FirstBooleanInputs
namespace Snake9.Regrowth.First112
noncomputable section
local instance blockDec43 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause1377 (q : Snake 81) (h : Conditions q) : valuation q 1696 = false ∨ valuation q 1698 = false ∨ valuation q 1702 = true := by
  have hs : count1699 q = (countLit q [-109, -110]) + (countLit q [-111, -113]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-109, -110]) (l₂ := [-111, -113])
  have hm := merge_two (literal (valuation q) (1696)) (literal (valuation q) (1698)) (literal (valuation q) (1702)) (countLit q [-109, -110]) (countLit q [-111, -113]) (count1699 q) 2 2 (meaning1696 q) (meaning1698 q) (meaning1702 q) hs
  change valuation q 1696 = false ∨ valuation q 1698 = false ∨ valuation q 1702 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1378 (q : Snake 81) (h : Conditions q) : valuation q 117 = true ∨ valuation q 1703 = true := by
  have hs : count1703 q = (countLit q [-116]) + (countLit q [-117]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-116]) (l₂ := [-117])
  have hm := merge_right (literal (valuation q) (-117)) (literal (valuation q) (1703)) (countLit q [-116]) (countLit q [-117]) (count1703 q) 1 (meaningNeg117 q) (meaning1703 q) hs
  change (! (valuation q 117)) = false ∨ valuation q 1703 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1379 (q : Snake 81) (h : Conditions q) : valuation q 116 = true ∨ valuation q 1703 = true := by
  have hs : count1703 q = (countLit q [-116]) + (countLit q [-117]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-116]) (l₂ := [-117])
  have hm := merge_left (literal (valuation q) (-116)) (literal (valuation q) (1703)) (countLit q [-116]) (countLit q [-117]) (count1703 q) 1 (meaningNeg116 q) (meaning1703 q) hs
  change (! (valuation q 116)) = false ∨ valuation q 1703 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1380 (q : Snake 81) (h : Conditions q) : valuation q 116 = true ∨ valuation q 117 = true ∨ valuation q 1704 = true := by
  have hs : count1703 q = (countLit q [-116]) + (countLit q [-117]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-116]) (l₂ := [-117])
  have hm := merge_two (literal (valuation q) (-116)) (literal (valuation q) (-117)) (literal (valuation q) (1704)) (countLit q [-116]) (countLit q [-117]) (count1703 q) 1 1 (meaningNeg116 q) (meaningNeg117 q) (meaning1704 q) hs
  change (! (valuation q 116)) = false ∨ (! (valuation q 117)) = false ∨ valuation q 1704 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1381 (q : Snake 81) (h : Conditions q) : valuation q 122 = true ∨ valuation q 1705 = true := by
  have hs : count1705 q = (countLit q [-119]) + (countLit q [-122]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-119]) (l₂ := [-122])
  have hm := merge_right (literal (valuation q) (-122)) (literal (valuation q) (1705)) (countLit q [-119]) (countLit q [-122]) (count1705 q) 1 (meaningNeg122 q) (meaning1705 q) hs
  change (! (valuation q 122)) = false ∨ valuation q 1705 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1382 (q : Snake 81) (h : Conditions q) : valuation q 119 = true ∨ valuation q 1705 = true := by
  have hs : count1705 q = (countLit q [-119]) + (countLit q [-122]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-119]) (l₂ := [-122])
  have hm := merge_left (literal (valuation q) (-119)) (literal (valuation q) (1705)) (countLit q [-119]) (countLit q [-122]) (count1705 q) 1 (meaningNeg119 q) (meaning1705 q) hs
  change (! (valuation q 119)) = false ∨ valuation q 1705 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1383 (q : Snake 81) (h : Conditions q) : valuation q 119 = true ∨ valuation q 122 = true ∨ valuation q 1706 = true := by
  have hs : count1705 q = (countLit q [-119]) + (countLit q [-122]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-119]) (l₂ := [-122])
  have hm := merge_two (literal (valuation q) (-119)) (literal (valuation q) (-122)) (literal (valuation q) (1706)) (countLit q [-119]) (countLit q [-122]) (count1705 q) 1 1 (meaningNeg119 q) (meaningNeg122 q) (meaning1706 q) hs
  change (! (valuation q 119)) = false ∨ (! (valuation q 122)) = false ∨ valuation q 1706 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1384 (q : Snake 81) (h : Conditions q) : valuation q 1705 = false ∨ valuation q 1707 = true := by
  have hs : count1707 q = (countLit q [-116, -117]) + (countLit q [-119, -122]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-116, -117]) (l₂ := [-119, -122])
  have hm := merge_right (literal (valuation q) (1705)) (literal (valuation q) (1707)) (countLit q [-116, -117]) (countLit q [-119, -122]) (count1707 q) 1 (meaning1705 q) (meaning1707 q) hs
  change valuation q 1705 = false ∨ valuation q 1707 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1385 (q : Snake 81) (h : Conditions q) : valuation q 1706 = false ∨ valuation q 1708 = true := by
  have hs : count1707 q = (countLit q [-116, -117]) + (countLit q [-119, -122]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-116, -117]) (l₂ := [-119, -122])
  have hm := merge_right (literal (valuation q) (1706)) (literal (valuation q) (1708)) (countLit q [-116, -117]) (countLit q [-119, -122]) (count1707 q) 2 (meaning1706 q) (meaning1708 q) hs
  change valuation q 1706 = false ∨ valuation q 1708 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1386 (q : Snake 81) (h : Conditions q) : valuation q 1703 = false ∨ valuation q 1707 = true := by
  have hs : count1707 q = (countLit q [-116, -117]) + (countLit q [-119, -122]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-116, -117]) (l₂ := [-119, -122])
  have hm := merge_left (literal (valuation q) (1703)) (literal (valuation q) (1707)) (countLit q [-116, -117]) (countLit q [-119, -122]) (count1707 q) 1 (meaning1703 q) (meaning1707 q) hs
  change valuation q 1703 = false ∨ valuation q 1707 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1387 (q : Snake 81) (h : Conditions q) : valuation q 1703 = false ∨ valuation q 1705 = false ∨ valuation q 1708 = true := by
  have hs : count1707 q = (countLit q [-116, -117]) + (countLit q [-119, -122]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-116, -117]) (l₂ := [-119, -122])
  have hm := merge_two (literal (valuation q) (1703)) (literal (valuation q) (1705)) (literal (valuation q) (1708)) (countLit q [-116, -117]) (countLit q [-119, -122]) (count1707 q) 1 1 (meaning1703 q) (meaning1705 q) (meaning1708 q) hs
  change valuation q 1703 = false ∨ valuation q 1705 = false ∨ valuation q 1708 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1388 (q : Snake 81) (h : Conditions q) : valuation q 1703 = false ∨ valuation q 1706 = false ∨ valuation q 1709 = true := by
  have hs : count1707 q = (countLit q [-116, -117]) + (countLit q [-119, -122]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-116, -117]) (l₂ := [-119, -122])
  have hm := merge_two (literal (valuation q) (1703)) (literal (valuation q) (1706)) (literal (valuation q) (1709)) (countLit q [-116, -117]) (countLit q [-119, -122]) (count1707 q) 1 2 (meaning1703 q) (meaning1706 q) (meaning1709 q) hs
  change valuation q 1703 = false ∨ valuation q 1706 = false ∨ valuation q 1709 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1389 (q : Snake 81) (h : Conditions q) : valuation q 1704 = false ∨ valuation q 1708 = true := by
  have hs : count1707 q = (countLit q [-116, -117]) + (countLit q [-119, -122]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-116, -117]) (l₂ := [-119, -122])
  have hm := merge_left (literal (valuation q) (1704)) (literal (valuation q) (1708)) (countLit q [-116, -117]) (countLit q [-119, -122]) (count1707 q) 2 (meaning1704 q) (meaning1708 q) hs
  change valuation q 1704 = false ∨ valuation q 1708 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1390 (q : Snake 81) (h : Conditions q) : valuation q 1704 = false ∨ valuation q 1705 = false ∨ valuation q 1709 = true := by
  have hs : count1707 q = (countLit q [-116, -117]) + (countLit q [-119, -122]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-116, -117]) (l₂ := [-119, -122])
  have hm := merge_two (literal (valuation q) (1704)) (literal (valuation q) (1705)) (literal (valuation q) (1709)) (countLit q [-116, -117]) (countLit q [-119, -122]) (count1707 q) 2 1 (meaning1704 q) (meaning1705 q) (meaning1709 q) hs
  change valuation q 1704 = false ∨ valuation q 1705 = false ∨ valuation q 1709 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1391 (q : Snake 81) (h : Conditions q) : valuation q 1704 = false ∨ valuation q 1706 = false ∨ valuation q 1710 = true := by
  have hs : count1707 q = (countLit q [-116, -117]) + (countLit q [-119, -122]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-116, -117]) (l₂ := [-119, -122])
  have hm := merge_two (literal (valuation q) (1704)) (literal (valuation q) (1706)) (literal (valuation q) (1710)) (countLit q [-116, -117]) (countLit q [-119, -122]) (count1707 q) 2 2 (meaning1704 q) (meaning1706 q) (meaning1710 q) hs
  change valuation q 1704 = false ∨ valuation q 1706 = false ∨ valuation q 1710 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1392 (q : Snake 81) (h : Conditions q) : valuation q 1707 = false ∨ valuation q 1711 = true := by
  have hs : count1711 q = (countLit q [-109, -110, -111, -113]) + (countLit q [-116, -117, -119, -122]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-109, -110, -111, -113]) (l₂ := [-116, -117, -119, -122])
  have hm := merge_right (literal (valuation q) (1707)) (literal (valuation q) (1711)) (countLit q [-109, -110, -111, -113]) (countLit q [-116, -117, -119, -122]) (count1711 q) 1 (meaning1707 q) (meaning1711 q) hs
  change valuation q 1707 = false ∨ valuation q 1711 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1393 (q : Snake 81) (h : Conditions q) : valuation q 1708 = false ∨ valuation q 1712 = true := by
  have hs : count1711 q = (countLit q [-109, -110, -111, -113]) + (countLit q [-116, -117, -119, -122]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-109, -110, -111, -113]) (l₂ := [-116, -117, -119, -122])
  have hm := merge_right (literal (valuation q) (1708)) (literal (valuation q) (1712)) (countLit q [-109, -110, -111, -113]) (countLit q [-116, -117, -119, -122]) (count1711 q) 2 (meaning1708 q) (meaning1712 q) hs
  change valuation q 1708 = false ∨ valuation q 1712 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1394 (q : Snake 81) (h : Conditions q) : valuation q 1709 = false ∨ valuation q 1713 = true := by
  have hs : count1711 q = (countLit q [-109, -110, -111, -113]) + (countLit q [-116, -117, -119, -122]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-109, -110, -111, -113]) (l₂ := [-116, -117, -119, -122])
  have hm := merge_right (literal (valuation q) (1709)) (literal (valuation q) (1713)) (countLit q [-109, -110, -111, -113]) (countLit q [-116, -117, -119, -122]) (count1711 q) 3 (meaning1709 q) (meaning1713 q) hs
  change valuation q 1709 = false ∨ valuation q 1713 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1395 (q : Snake 81) (h : Conditions q) : valuation q 1710 = false ∨ valuation q 1714 = true := by
  have hs : count1711 q = (countLit q [-109, -110, -111, -113]) + (countLit q [-116, -117, -119, -122]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-109, -110, -111, -113]) (l₂ := [-116, -117, -119, -122])
  have hm := merge_right (literal (valuation q) (1710)) (literal (valuation q) (1714)) (countLit q [-109, -110, -111, -113]) (countLit q [-116, -117, -119, -122]) (count1711 q) 4 (meaning1710 q) (meaning1714 q) hs
  change valuation q 1710 = false ∨ valuation q 1714 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1396 (q : Snake 81) (h : Conditions q) : valuation q 1699 = false ∨ valuation q 1711 = true := by
  have hs : count1711 q = (countLit q [-109, -110, -111, -113]) + (countLit q [-116, -117, -119, -122]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-109, -110, -111, -113]) (l₂ := [-116, -117, -119, -122])
  have hm := merge_left (literal (valuation q) (1699)) (literal (valuation q) (1711)) (countLit q [-109, -110, -111, -113]) (countLit q [-116, -117, -119, -122]) (count1711 q) 1 (meaning1699 q) (meaning1711 q) hs
  change valuation q 1699 = false ∨ valuation q 1711 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1397 (q : Snake 81) (h : Conditions q) : valuation q 1699 = false ∨ valuation q 1707 = false ∨ valuation q 1712 = true := by
  have hs : count1711 q = (countLit q [-109, -110, -111, -113]) + (countLit q [-116, -117, -119, -122]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-109, -110, -111, -113]) (l₂ := [-116, -117, -119, -122])
  have hm := merge_two (literal (valuation q) (1699)) (literal (valuation q) (1707)) (literal (valuation q) (1712)) (countLit q [-109, -110, -111, -113]) (countLit q [-116, -117, -119, -122]) (count1711 q) 1 1 (meaning1699 q) (meaning1707 q) (meaning1712 q) hs
  change valuation q 1699 = false ∨ valuation q 1707 = false ∨ valuation q 1712 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1398 (q : Snake 81) (h : Conditions q) : valuation q 1699 = false ∨ valuation q 1708 = false ∨ valuation q 1713 = true := by
  have hs : count1711 q = (countLit q [-109, -110, -111, -113]) + (countLit q [-116, -117, -119, -122]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-109, -110, -111, -113]) (l₂ := [-116, -117, -119, -122])
  have hm := merge_two (literal (valuation q) (1699)) (literal (valuation q) (1708)) (literal (valuation q) (1713)) (countLit q [-109, -110, -111, -113]) (countLit q [-116, -117, -119, -122]) (count1711 q) 1 2 (meaning1699 q) (meaning1708 q) (meaning1713 q) hs
  change valuation q 1699 = false ∨ valuation q 1708 = false ∨ valuation q 1713 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1399 (q : Snake 81) (h : Conditions q) : valuation q 1699 = false ∨ valuation q 1709 = false ∨ valuation q 1714 = true := by
  have hs : count1711 q = (countLit q [-109, -110, -111, -113]) + (countLit q [-116, -117, -119, -122]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-109, -110, -111, -113]) (l₂ := [-116, -117, -119, -122])
  have hm := merge_two (literal (valuation q) (1699)) (literal (valuation q) (1709)) (literal (valuation q) (1714)) (countLit q [-109, -110, -111, -113]) (countLit q [-116, -117, -119, -122]) (count1711 q) 1 3 (meaning1699 q) (meaning1709 q) (meaning1714 q) hs
  change valuation q 1699 = false ∨ valuation q 1709 = false ∨ valuation q 1714 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1400 (q : Snake 81) (h : Conditions q) : valuation q 1699 = false ∨ valuation q 1710 = false ∨ valuation q 1715 = true := by
  have hs : count1711 q = (countLit q [-109, -110, -111, -113]) + (countLit q [-116, -117, -119, -122]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-109, -110, -111, -113]) (l₂ := [-116, -117, -119, -122])
  have hm := merge_two (literal (valuation q) (1699)) (literal (valuation q) (1710)) (literal (valuation q) (1715)) (countLit q [-109, -110, -111, -113]) (countLit q [-116, -117, -119, -122]) (count1711 q) 1 4 (meaning1699 q) (meaning1710 q) (meaning1715 q) hs
  change valuation q 1699 = false ∨ valuation q 1710 = false ∨ valuation q 1715 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1401 (q : Snake 81) (h : Conditions q) : valuation q 1700 = false ∨ valuation q 1712 = true := by
  have hs : count1711 q = (countLit q [-109, -110, -111, -113]) + (countLit q [-116, -117, -119, -122]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-109, -110, -111, -113]) (l₂ := [-116, -117, -119, -122])
  have hm := merge_left (literal (valuation q) (1700)) (literal (valuation q) (1712)) (countLit q [-109, -110, -111, -113]) (countLit q [-116, -117, -119, -122]) (count1711 q) 2 (meaning1700 q) (meaning1712 q) hs
  change valuation q 1700 = false ∨ valuation q 1712 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1402 (q : Snake 81) (h : Conditions q) : valuation q 1700 = false ∨ valuation q 1707 = false ∨ valuation q 1713 = true := by
  have hs : count1711 q = (countLit q [-109, -110, -111, -113]) + (countLit q [-116, -117, -119, -122]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-109, -110, -111, -113]) (l₂ := [-116, -117, -119, -122])
  have hm := merge_two (literal (valuation q) (1700)) (literal (valuation q) (1707)) (literal (valuation q) (1713)) (countLit q [-109, -110, -111, -113]) (countLit q [-116, -117, -119, -122]) (count1711 q) 2 1 (meaning1700 q) (meaning1707 q) (meaning1713 q) hs
  change valuation q 1700 = false ∨ valuation q 1707 = false ∨ valuation q 1713 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1403 (q : Snake 81) (h : Conditions q) : valuation q 1700 = false ∨ valuation q 1708 = false ∨ valuation q 1714 = true := by
  have hs : count1711 q = (countLit q [-109, -110, -111, -113]) + (countLit q [-116, -117, -119, -122]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-109, -110, -111, -113]) (l₂ := [-116, -117, -119, -122])
  have hm := merge_two (literal (valuation q) (1700)) (literal (valuation q) (1708)) (literal (valuation q) (1714)) (countLit q [-109, -110, -111, -113]) (countLit q [-116, -117, -119, -122]) (count1711 q) 2 2 (meaning1700 q) (meaning1708 q) (meaning1714 q) hs
  change valuation q 1700 = false ∨ valuation q 1708 = false ∨ valuation q 1714 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1404 (q : Snake 81) (h : Conditions q) : valuation q 1700 = false ∨ valuation q 1709 = false ∨ valuation q 1715 = true := by
  have hs : count1711 q = (countLit q [-109, -110, -111, -113]) + (countLit q [-116, -117, -119, -122]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-109, -110, -111, -113]) (l₂ := [-116, -117, -119, -122])
  have hm := merge_two (literal (valuation q) (1700)) (literal (valuation q) (1709)) (literal (valuation q) (1715)) (countLit q [-109, -110, -111, -113]) (countLit q [-116, -117, -119, -122]) (count1711 q) 2 3 (meaning1700 q) (meaning1709 q) (meaning1715 q) hs
  change valuation q 1700 = false ∨ valuation q 1709 = false ∨ valuation q 1715 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1405 (q : Snake 81) (h : Conditions q) : valuation q 1700 = false ∨ valuation q 1710 = false ∨ valuation q 1716 = true := by
  have hs : count1711 q = (countLit q [-109, -110, -111, -113]) + (countLit q [-116, -117, -119, -122]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-109, -110, -111, -113]) (l₂ := [-116, -117, -119, -122])
  have hm := merge_two (literal (valuation q) (1700)) (literal (valuation q) (1710)) (literal (valuation q) (1716)) (countLit q [-109, -110, -111, -113]) (countLit q [-116, -117, -119, -122]) (count1711 q) 2 4 (meaning1700 q) (meaning1710 q) (meaning1716 q) hs
  change valuation q 1700 = false ∨ valuation q 1710 = false ∨ valuation q 1716 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1406 (q : Snake 81) (h : Conditions q) : valuation q 1701 = false ∨ valuation q 1713 = true := by
  have hs : count1711 q = (countLit q [-109, -110, -111, -113]) + (countLit q [-116, -117, -119, -122]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-109, -110, -111, -113]) (l₂ := [-116, -117, -119, -122])
  have hm := merge_left (literal (valuation q) (1701)) (literal (valuation q) (1713)) (countLit q [-109, -110, -111, -113]) (countLit q [-116, -117, -119, -122]) (count1711 q) 3 (meaning1701 q) (meaning1713 q) hs
  change valuation q 1701 = false ∨ valuation q 1713 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1407 (q : Snake 81) (h : Conditions q) : valuation q 1701 = false ∨ valuation q 1707 = false ∨ valuation q 1714 = true := by
  have hs : count1711 q = (countLit q [-109, -110, -111, -113]) + (countLit q [-116, -117, -119, -122]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-109, -110, -111, -113]) (l₂ := [-116, -117, -119, -122])
  have hm := merge_two (literal (valuation q) (1701)) (literal (valuation q) (1707)) (literal (valuation q) (1714)) (countLit q [-109, -110, -111, -113]) (countLit q [-116, -117, -119, -122]) (count1711 q) 3 1 (meaning1701 q) (meaning1707 q) (meaning1714 q) hs
  change valuation q 1701 = false ∨ valuation q 1707 = false ∨ valuation q 1714 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1408 (q : Snake 81) (h : Conditions q) : valuation q 1701 = false ∨ valuation q 1708 = false ∨ valuation q 1715 = true := by
  have hs : count1711 q = (countLit q [-109, -110, -111, -113]) + (countLit q [-116, -117, -119, -122]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-109, -110, -111, -113]) (l₂ := [-116, -117, -119, -122])
  have hm := merge_two (literal (valuation q) (1701)) (literal (valuation q) (1708)) (literal (valuation q) (1715)) (countLit q [-109, -110, -111, -113]) (countLit q [-116, -117, -119, -122]) (count1711 q) 3 2 (meaning1701 q) (meaning1708 q) (meaning1715 q) hs
  change valuation q 1701 = false ∨ valuation q 1708 = false ∨ valuation q 1715 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem block43 (q : Snake 81) (h : Conditions q) : Dfs112FirstBoolean.Block43 (valuation q) :=
  ⟨clause1377 q h, clause1378 q h, clause1379 q h, clause1380 q h, clause1381 q h, clause1382 q h, clause1383 q h, clause1384 q h, clause1385 q h, clause1386 q h, clause1387 q h, clause1388 q h, clause1389 q h, clause1390 q h, clause1391 q h, clause1392 q h, clause1393 q h, clause1394 q h, clause1395 q h, clause1396 q h, clause1397 q h, clause1398 q h, clause1399 q h, clause1400 q h, clause1401 q h, clause1402 q h, clause1403 q h, clause1404 q h, clause1405 q h, clause1406 q h, clause1407 q h, clause1408 q h⟩

end
end Snake9.Regrowth.First112
