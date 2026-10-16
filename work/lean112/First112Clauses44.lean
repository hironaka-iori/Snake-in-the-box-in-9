import First112Semantics
import Dfs112FirstBooleanInputs
namespace Snake9.Regrowth.First112
noncomputable section
local instance blockDec44 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause1409 (q : Snake 81) (h : Conditions q) : valuation q 1701 = false ∨ valuation q 1709 = false ∨ valuation q 1716 = true := by
  have hs : count1711 q = (countLit q [-109, -110, -111, -113]) + (countLit q [-116, -117, -119, -122]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-109, -110, -111, -113]) (l₂ := [-116, -117, -119, -122])
  have hm := merge_two (literal (valuation q) (1701)) (literal (valuation q) (1709)) (literal (valuation q) (1716)) (countLit q [-109, -110, -111, -113]) (countLit q [-116, -117, -119, -122]) (count1711 q) 3 3 (meaning1701 q) (meaning1709 q) (meaning1716 q) hs
  change valuation q 1701 = false ∨ valuation q 1709 = false ∨ valuation q 1716 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1410 (q : Snake 81) (h : Conditions q) : valuation q 1702 = false ∨ valuation q 1714 = true := by
  have hs : count1711 q = (countLit q [-109, -110, -111, -113]) + (countLit q [-116, -117, -119, -122]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-109, -110, -111, -113]) (l₂ := [-116, -117, -119, -122])
  have hm := merge_left (literal (valuation q) (1702)) (literal (valuation q) (1714)) (countLit q [-109, -110, -111, -113]) (countLit q [-116, -117, -119, -122]) (count1711 q) 4 (meaning1702 q) (meaning1714 q) hs
  change valuation q 1702 = false ∨ valuation q 1714 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1411 (q : Snake 81) (h : Conditions q) : valuation q 1702 = false ∨ valuation q 1707 = false ∨ valuation q 1715 = true := by
  have hs : count1711 q = (countLit q [-109, -110, -111, -113]) + (countLit q [-116, -117, -119, -122]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-109, -110, -111, -113]) (l₂ := [-116, -117, -119, -122])
  have hm := merge_two (literal (valuation q) (1702)) (literal (valuation q) (1707)) (literal (valuation q) (1715)) (countLit q [-109, -110, -111, -113]) (countLit q [-116, -117, -119, -122]) (count1711 q) 4 1 (meaning1702 q) (meaning1707 q) (meaning1715 q) hs
  change valuation q 1702 = false ∨ valuation q 1707 = false ∨ valuation q 1715 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1412 (q : Snake 81) (h : Conditions q) : valuation q 1687 = false ∨ valuation q 1712 = false ∨ valuation q 1721 = true := by
  have hs : count1719 q = (countLit q [-92, -93, -95, -97, -98, -101, -104, -105]) + (countLit q [-109, -110, -111, -113, -116, -117, -119, -122]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-92, -93, -95, -97, -98, -101, -104, -105]) (l₂ := [-109, -110, -111, -113, -116, -117, -119, -122])
  have hm := merge_two (literal (valuation q) (1687)) (literal (valuation q) (1712)) (literal (valuation q) (1721)) (countLit q [-92, -93, -95, -97, -98, -101, -104, -105]) (countLit q [-109, -110, -111, -113, -116, -117, -119, -122]) (count1719 q) 1 2 (meaning1687 q) (meaning1712 q) (meaning1721 q) hs
  change valuation q 1687 = false ∨ valuation q 1712 = false ∨ valuation q 1721 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1413 (q : Snake 81) (h : Conditions q) : valuation q 1687 = false ∨ valuation q 1713 = false ∨ valuation q 1722 = true := by
  have hs : count1719 q = (countLit q [-92, -93, -95, -97, -98, -101, -104, -105]) + (countLit q [-109, -110, -111, -113, -116, -117, -119, -122]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-92, -93, -95, -97, -98, -101, -104, -105]) (l₂ := [-109, -110, -111, -113, -116, -117, -119, -122])
  have hm := merge_two (literal (valuation q) (1687)) (literal (valuation q) (1713)) (literal (valuation q) (1722)) (countLit q [-92, -93, -95, -97, -98, -101, -104, -105]) (countLit q [-109, -110, -111, -113, -116, -117, -119, -122]) (count1719 q) 1 3 (meaning1687 q) (meaning1713 q) (meaning1722 q) hs
  change valuation q 1687 = false ∨ valuation q 1713 = false ∨ valuation q 1722 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1414 (q : Snake 81) (h : Conditions q) : valuation q 1687 = false ∨ valuation q 1714 = false ∨ valuation q 1723 = true := by
  have hs : count1719 q = (countLit q [-92, -93, -95, -97, -98, -101, -104, -105]) + (countLit q [-109, -110, -111, -113, -116, -117, -119, -122]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-92, -93, -95, -97, -98, -101, -104, -105]) (l₂ := [-109, -110, -111, -113, -116, -117, -119, -122])
  have hm := merge_two (literal (valuation q) (1687)) (literal (valuation q) (1714)) (literal (valuation q) (1723)) (countLit q [-92, -93, -95, -97, -98, -101, -104, -105]) (countLit q [-109, -110, -111, -113, -116, -117, -119, -122]) (count1719 q) 1 4 (meaning1687 q) (meaning1714 q) (meaning1723 q) hs
  change valuation q 1687 = false ∨ valuation q 1714 = false ∨ valuation q 1723 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1415 (q : Snake 81) (h : Conditions q) : valuation q 1687 = false ∨ valuation q 1715 = false ∨ valuation q 1724 = true := by
  have hs : count1719 q = (countLit q [-92, -93, -95, -97, -98, -101, -104, -105]) + (countLit q [-109, -110, -111, -113, -116, -117, -119, -122]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-92, -93, -95, -97, -98, -101, -104, -105]) (l₂ := [-109, -110, -111, -113, -116, -117, -119, -122])
  have hm := merge_two (literal (valuation q) (1687)) (literal (valuation q) (1715)) (literal (valuation q) (1724)) (countLit q [-92, -93, -95, -97, -98, -101, -104, -105]) (countLit q [-109, -110, -111, -113, -116, -117, -119, -122]) (count1719 q) 1 5 (meaning1687 q) (meaning1715 q) (meaning1724 q) hs
  change valuation q 1687 = false ∨ valuation q 1715 = false ∨ valuation q 1724 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1416 (q : Snake 81) (h : Conditions q) : valuation q 1687 = false ∨ valuation q 1716 = false ∨ valuation q 1725 = true := by
  have hs : count1719 q = (countLit q [-92, -93, -95, -97, -98, -101, -104, -105]) + (countLit q [-109, -110, -111, -113, -116, -117, -119, -122]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-92, -93, -95, -97, -98, -101, -104, -105]) (l₂ := [-109, -110, -111, -113, -116, -117, -119, -122])
  have hm := merge_two (literal (valuation q) (1687)) (literal (valuation q) (1716)) (literal (valuation q) (1725)) (countLit q [-92, -93, -95, -97, -98, -101, -104, -105]) (countLit q [-109, -110, -111, -113, -116, -117, -119, -122]) (count1719 q) 1 6 (meaning1687 q) (meaning1716 q) (meaning1725 q) hs
  change valuation q 1687 = false ∨ valuation q 1716 = false ∨ valuation q 1725 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1417 (q : Snake 81) (h : Conditions q) : valuation q 1688 = false ∨ valuation q 1711 = false ∨ valuation q 1721 = true := by
  have hs : count1719 q = (countLit q [-92, -93, -95, -97, -98, -101, -104, -105]) + (countLit q [-109, -110, -111, -113, -116, -117, -119, -122]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-92, -93, -95, -97, -98, -101, -104, -105]) (l₂ := [-109, -110, -111, -113, -116, -117, -119, -122])
  have hm := merge_two (literal (valuation q) (1688)) (literal (valuation q) (1711)) (literal (valuation q) (1721)) (countLit q [-92, -93, -95, -97, -98, -101, -104, -105]) (countLit q [-109, -110, -111, -113, -116, -117, -119, -122]) (count1719 q) 2 1 (meaning1688 q) (meaning1711 q) (meaning1721 q) hs
  change valuation q 1688 = false ∨ valuation q 1711 = false ∨ valuation q 1721 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1418 (q : Snake 81) (h : Conditions q) : valuation q 1688 = false ∨ valuation q 1712 = false ∨ valuation q 1722 = true := by
  have hs : count1719 q = (countLit q [-92, -93, -95, -97, -98, -101, -104, -105]) + (countLit q [-109, -110, -111, -113, -116, -117, -119, -122]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-92, -93, -95, -97, -98, -101, -104, -105]) (l₂ := [-109, -110, -111, -113, -116, -117, -119, -122])
  have hm := merge_two (literal (valuation q) (1688)) (literal (valuation q) (1712)) (literal (valuation q) (1722)) (countLit q [-92, -93, -95, -97, -98, -101, -104, -105]) (countLit q [-109, -110, -111, -113, -116, -117, -119, -122]) (count1719 q) 2 2 (meaning1688 q) (meaning1712 q) (meaning1722 q) hs
  change valuation q 1688 = false ∨ valuation q 1712 = false ∨ valuation q 1722 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1419 (q : Snake 81) (h : Conditions q) : valuation q 1688 = false ∨ valuation q 1713 = false ∨ valuation q 1723 = true := by
  have hs : count1719 q = (countLit q [-92, -93, -95, -97, -98, -101, -104, -105]) + (countLit q [-109, -110, -111, -113, -116, -117, -119, -122]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-92, -93, -95, -97, -98, -101, -104, -105]) (l₂ := [-109, -110, -111, -113, -116, -117, -119, -122])
  have hm := merge_two (literal (valuation q) (1688)) (literal (valuation q) (1713)) (literal (valuation q) (1723)) (countLit q [-92, -93, -95, -97, -98, -101, -104, -105]) (countLit q [-109, -110, -111, -113, -116, -117, -119, -122]) (count1719 q) 2 3 (meaning1688 q) (meaning1713 q) (meaning1723 q) hs
  change valuation q 1688 = false ∨ valuation q 1713 = false ∨ valuation q 1723 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1420 (q : Snake 81) (h : Conditions q) : valuation q 1688 = false ∨ valuation q 1714 = false ∨ valuation q 1724 = true := by
  have hs : count1719 q = (countLit q [-92, -93, -95, -97, -98, -101, -104, -105]) + (countLit q [-109, -110, -111, -113, -116, -117, -119, -122]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-92, -93, -95, -97, -98, -101, -104, -105]) (l₂ := [-109, -110, -111, -113, -116, -117, -119, -122])
  have hm := merge_two (literal (valuation q) (1688)) (literal (valuation q) (1714)) (literal (valuation q) (1724)) (countLit q [-92, -93, -95, -97, -98, -101, -104, -105]) (countLit q [-109, -110, -111, -113, -116, -117, -119, -122]) (count1719 q) 2 4 (meaning1688 q) (meaning1714 q) (meaning1724 q) hs
  change valuation q 1688 = false ∨ valuation q 1714 = false ∨ valuation q 1724 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1421 (q : Snake 81) (h : Conditions q) : valuation q 1688 = false ∨ valuation q 1715 = false ∨ valuation q 1725 = true := by
  have hs : count1719 q = (countLit q [-92, -93, -95, -97, -98, -101, -104, -105]) + (countLit q [-109, -110, -111, -113, -116, -117, -119, -122]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-92, -93, -95, -97, -98, -101, -104, -105]) (l₂ := [-109, -110, -111, -113, -116, -117, -119, -122])
  have hm := merge_two (literal (valuation q) (1688)) (literal (valuation q) (1715)) (literal (valuation q) (1725)) (countLit q [-92, -93, -95, -97, -98, -101, -104, -105]) (countLit q [-109, -110, -111, -113, -116, -117, -119, -122]) (count1719 q) 2 5 (meaning1688 q) (meaning1715 q) (meaning1725 q) hs
  change valuation q 1688 = false ∨ valuation q 1715 = false ∨ valuation q 1725 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1422 (q : Snake 81) (h : Conditions q) : valuation q 1688 = false ∨ valuation q 1716 = false ∨ valuation q 1726 = true := by
  have hs : count1719 q = (countLit q [-92, -93, -95, -97, -98, -101, -104, -105]) + (countLit q [-109, -110, -111, -113, -116, -117, -119, -122]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-92, -93, -95, -97, -98, -101, -104, -105]) (l₂ := [-109, -110, -111, -113, -116, -117, -119, -122])
  have hm := merge_two (literal (valuation q) (1688)) (literal (valuation q) (1716)) (literal (valuation q) (1726)) (countLit q [-92, -93, -95, -97, -98, -101, -104, -105]) (countLit q [-109, -110, -111, -113, -116, -117, -119, -122]) (count1719 q) 2 6 (meaning1688 q) (meaning1716 q) (meaning1726 q) hs
  change valuation q 1688 = false ∨ valuation q 1716 = false ∨ valuation q 1726 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1423 (q : Snake 81) (h : Conditions q) : valuation q 1689 = false ∨ valuation q 1711 = false ∨ valuation q 1722 = true := by
  have hs : count1719 q = (countLit q [-92, -93, -95, -97, -98, -101, -104, -105]) + (countLit q [-109, -110, -111, -113, -116, -117, -119, -122]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-92, -93, -95, -97, -98, -101, -104, -105]) (l₂ := [-109, -110, -111, -113, -116, -117, -119, -122])
  have hm := merge_two (literal (valuation q) (1689)) (literal (valuation q) (1711)) (literal (valuation q) (1722)) (countLit q [-92, -93, -95, -97, -98, -101, -104, -105]) (countLit q [-109, -110, -111, -113, -116, -117, -119, -122]) (count1719 q) 3 1 (meaning1689 q) (meaning1711 q) (meaning1722 q) hs
  change valuation q 1689 = false ∨ valuation q 1711 = false ∨ valuation q 1722 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1424 (q : Snake 81) (h : Conditions q) : valuation q 1689 = false ∨ valuation q 1712 = false ∨ valuation q 1723 = true := by
  have hs : count1719 q = (countLit q [-92, -93, -95, -97, -98, -101, -104, -105]) + (countLit q [-109, -110, -111, -113, -116, -117, -119, -122]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-92, -93, -95, -97, -98, -101, -104, -105]) (l₂ := [-109, -110, -111, -113, -116, -117, -119, -122])
  have hm := merge_two (literal (valuation q) (1689)) (literal (valuation q) (1712)) (literal (valuation q) (1723)) (countLit q [-92, -93, -95, -97, -98, -101, -104, -105]) (countLit q [-109, -110, -111, -113, -116, -117, -119, -122]) (count1719 q) 3 2 (meaning1689 q) (meaning1712 q) (meaning1723 q) hs
  change valuation q 1689 = false ∨ valuation q 1712 = false ∨ valuation q 1723 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1425 (q : Snake 81) (h : Conditions q) : valuation q 1689 = false ∨ valuation q 1713 = false ∨ valuation q 1724 = true := by
  have hs : count1719 q = (countLit q [-92, -93, -95, -97, -98, -101, -104, -105]) + (countLit q [-109, -110, -111, -113, -116, -117, -119, -122]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-92, -93, -95, -97, -98, -101, -104, -105]) (l₂ := [-109, -110, -111, -113, -116, -117, -119, -122])
  have hm := merge_two (literal (valuation q) (1689)) (literal (valuation q) (1713)) (literal (valuation q) (1724)) (countLit q [-92, -93, -95, -97, -98, -101, -104, -105]) (countLit q [-109, -110, -111, -113, -116, -117, -119, -122]) (count1719 q) 3 3 (meaning1689 q) (meaning1713 q) (meaning1724 q) hs
  change valuation q 1689 = false ∨ valuation q 1713 = false ∨ valuation q 1724 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1426 (q : Snake 81) (h : Conditions q) : valuation q 1689 = false ∨ valuation q 1714 = false ∨ valuation q 1725 = true := by
  have hs : count1719 q = (countLit q [-92, -93, -95, -97, -98, -101, -104, -105]) + (countLit q [-109, -110, -111, -113, -116, -117, -119, -122]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-92, -93, -95, -97, -98, -101, -104, -105]) (l₂ := [-109, -110, -111, -113, -116, -117, -119, -122])
  have hm := merge_two (literal (valuation q) (1689)) (literal (valuation q) (1714)) (literal (valuation q) (1725)) (countLit q [-92, -93, -95, -97, -98, -101, -104, -105]) (countLit q [-109, -110, -111, -113, -116, -117, -119, -122]) (count1719 q) 3 4 (meaning1689 q) (meaning1714 q) (meaning1725 q) hs
  change valuation q 1689 = false ∨ valuation q 1714 = false ∨ valuation q 1725 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1427 (q : Snake 81) (h : Conditions q) : valuation q 1689 = false ∨ valuation q 1715 = false ∨ valuation q 1726 = true := by
  have hs : count1719 q = (countLit q [-92, -93, -95, -97, -98, -101, -104, -105]) + (countLit q [-109, -110, -111, -113, -116, -117, -119, -122]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-92, -93, -95, -97, -98, -101, -104, -105]) (l₂ := [-109, -110, -111, -113, -116, -117, -119, -122])
  have hm := merge_two (literal (valuation q) (1689)) (literal (valuation q) (1715)) (literal (valuation q) (1726)) (countLit q [-92, -93, -95, -97, -98, -101, -104, -105]) (countLit q [-109, -110, -111, -113, -116, -117, -119, -122]) (count1719 q) 3 5 (meaning1689 q) (meaning1715 q) (meaning1726 q) hs
  change valuation q 1689 = false ∨ valuation q 1715 = false ∨ valuation q 1726 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1428 (q : Snake 81) (h : Conditions q) : valuation q 1690 = false ∨ valuation q 1711 = false ∨ valuation q 1723 = true := by
  have hs : count1719 q = (countLit q [-92, -93, -95, -97, -98, -101, -104, -105]) + (countLit q [-109, -110, -111, -113, -116, -117, -119, -122]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-92, -93, -95, -97, -98, -101, -104, -105]) (l₂ := [-109, -110, -111, -113, -116, -117, -119, -122])
  have hm := merge_two (literal (valuation q) (1690)) (literal (valuation q) (1711)) (literal (valuation q) (1723)) (countLit q [-92, -93, -95, -97, -98, -101, -104, -105]) (countLit q [-109, -110, -111, -113, -116, -117, -119, -122]) (count1719 q) 4 1 (meaning1690 q) (meaning1711 q) (meaning1723 q) hs
  change valuation q 1690 = false ∨ valuation q 1711 = false ∨ valuation q 1723 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1429 (q : Snake 81) (h : Conditions q) : valuation q 1690 = false ∨ valuation q 1712 = false ∨ valuation q 1724 = true := by
  have hs : count1719 q = (countLit q [-92, -93, -95, -97, -98, -101, -104, -105]) + (countLit q [-109, -110, -111, -113, -116, -117, -119, -122]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-92, -93, -95, -97, -98, -101, -104, -105]) (l₂ := [-109, -110, -111, -113, -116, -117, -119, -122])
  have hm := merge_two (literal (valuation q) (1690)) (literal (valuation q) (1712)) (literal (valuation q) (1724)) (countLit q [-92, -93, -95, -97, -98, -101, -104, -105]) (countLit q [-109, -110, -111, -113, -116, -117, -119, -122]) (count1719 q) 4 2 (meaning1690 q) (meaning1712 q) (meaning1724 q) hs
  change valuation q 1690 = false ∨ valuation q 1712 = false ∨ valuation q 1724 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1430 (q : Snake 81) (h : Conditions q) : valuation q 1690 = false ∨ valuation q 1713 = false ∨ valuation q 1725 = true := by
  have hs : count1719 q = (countLit q [-92, -93, -95, -97, -98, -101, -104, -105]) + (countLit q [-109, -110, -111, -113, -116, -117, -119, -122]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-92, -93, -95, -97, -98, -101, -104, -105]) (l₂ := [-109, -110, -111, -113, -116, -117, -119, -122])
  have hm := merge_two (literal (valuation q) (1690)) (literal (valuation q) (1713)) (literal (valuation q) (1725)) (countLit q [-92, -93, -95, -97, -98, -101, -104, -105]) (countLit q [-109, -110, -111, -113, -116, -117, -119, -122]) (count1719 q) 4 3 (meaning1690 q) (meaning1713 q) (meaning1725 q) hs
  change valuation q 1690 = false ∨ valuation q 1713 = false ∨ valuation q 1725 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1431 (q : Snake 81) (h : Conditions q) : valuation q 1690 = false ∨ valuation q 1714 = false ∨ valuation q 1726 = true := by
  have hs : count1719 q = (countLit q [-92, -93, -95, -97, -98, -101, -104, -105]) + (countLit q [-109, -110, -111, -113, -116, -117, -119, -122]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-92, -93, -95, -97, -98, -101, -104, -105]) (l₂ := [-109, -110, -111, -113, -116, -117, -119, -122])
  have hm := merge_two (literal (valuation q) (1690)) (literal (valuation q) (1714)) (literal (valuation q) (1726)) (countLit q [-92, -93, -95, -97, -98, -101, -104, -105]) (countLit q [-109, -110, -111, -113, -116, -117, -119, -122]) (count1719 q) 4 4 (meaning1690 q) (meaning1714 q) (meaning1726 q) hs
  change valuation q 1690 = false ∨ valuation q 1714 = false ∨ valuation q 1726 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1432 (q : Snake 81) (h : Conditions q) : valuation q 1690 = false ∨ valuation q 1715 = false ∨ valuation q 1727 = true := by
  have hs : count1719 q = (countLit q [-92, -93, -95, -97, -98, -101, -104, -105]) + (countLit q [-109, -110, -111, -113, -116, -117, -119, -122]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-92, -93, -95, -97, -98, -101, -104, -105]) (l₂ := [-109, -110, -111, -113, -116, -117, -119, -122])
  have hm := merge_two (literal (valuation q) (1690)) (literal (valuation q) (1715)) (literal (valuation q) (1727)) (countLit q [-92, -93, -95, -97, -98, -101, -104, -105]) (countLit q [-109, -110, -111, -113, -116, -117, -119, -122]) (count1719 q) 4 5 (meaning1690 q) (meaning1715 q) (meaning1727 q) hs
  change valuation q 1690 = false ∨ valuation q 1715 = false ∨ valuation q 1727 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1433 (q : Snake 81) (h : Conditions q) : valuation q 1690 = false ∨ valuation q 1716 = false ∨ valuation q 1728 = true := by
  have hs : count1719 q = (countLit q [-92, -93, -95, -97, -98, -101, -104, -105]) + (countLit q [-109, -110, -111, -113, -116, -117, -119, -122]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-92, -93, -95, -97, -98, -101, -104, -105]) (l₂ := [-109, -110, -111, -113, -116, -117, -119, -122])
  have hm := merge_two (literal (valuation q) (1690)) (literal (valuation q) (1716)) (literal (valuation q) (1728)) (countLit q [-92, -93, -95, -97, -98, -101, -104, -105]) (countLit q [-109, -110, -111, -113, -116, -117, -119, -122]) (count1719 q) 4 6 (meaning1690 q) (meaning1716 q) (meaning1728 q) hs
  change valuation q 1690 = false ∨ valuation q 1716 = false ∨ valuation q 1728 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1434 (q : Snake 81) (h : Conditions q) : valuation q 1691 = false ∨ valuation q 1711 = false ∨ valuation q 1724 = true := by
  have hs : count1719 q = (countLit q [-92, -93, -95, -97, -98, -101, -104, -105]) + (countLit q [-109, -110, -111, -113, -116, -117, -119, -122]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-92, -93, -95, -97, -98, -101, -104, -105]) (l₂ := [-109, -110, -111, -113, -116, -117, -119, -122])
  have hm := merge_two (literal (valuation q) (1691)) (literal (valuation q) (1711)) (literal (valuation q) (1724)) (countLit q [-92, -93, -95, -97, -98, -101, -104, -105]) (countLit q [-109, -110, -111, -113, -116, -117, -119, -122]) (count1719 q) 5 1 (meaning1691 q) (meaning1711 q) (meaning1724 q) hs
  change valuation q 1691 = false ∨ valuation q 1711 = false ∨ valuation q 1724 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1435 (q : Snake 81) (h : Conditions q) : valuation q 1691 = false ∨ valuation q 1712 = false ∨ valuation q 1725 = true := by
  have hs : count1719 q = (countLit q [-92, -93, -95, -97, -98, -101, -104, -105]) + (countLit q [-109, -110, -111, -113, -116, -117, -119, -122]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-92, -93, -95, -97, -98, -101, -104, -105]) (l₂ := [-109, -110, -111, -113, -116, -117, -119, -122])
  have hm := merge_two (literal (valuation q) (1691)) (literal (valuation q) (1712)) (literal (valuation q) (1725)) (countLit q [-92, -93, -95, -97, -98, -101, -104, -105]) (countLit q [-109, -110, -111, -113, -116, -117, -119, -122]) (count1719 q) 5 2 (meaning1691 q) (meaning1712 q) (meaning1725 q) hs
  change valuation q 1691 = false ∨ valuation q 1712 = false ∨ valuation q 1725 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1436 (q : Snake 81) (h : Conditions q) : valuation q 1691 = false ∨ valuation q 1713 = false ∨ valuation q 1726 = true := by
  have hs : count1719 q = (countLit q [-92, -93, -95, -97, -98, -101, -104, -105]) + (countLit q [-109, -110, -111, -113, -116, -117, -119, -122]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-92, -93, -95, -97, -98, -101, -104, -105]) (l₂ := [-109, -110, -111, -113, -116, -117, -119, -122])
  have hm := merge_two (literal (valuation q) (1691)) (literal (valuation q) (1713)) (literal (valuation q) (1726)) (countLit q [-92, -93, -95, -97, -98, -101, -104, -105]) (countLit q [-109, -110, -111, -113, -116, -117, -119, -122]) (count1719 q) 5 3 (meaning1691 q) (meaning1713 q) (meaning1726 q) hs
  change valuation q 1691 = false ∨ valuation q 1713 = false ∨ valuation q 1726 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1437 (q : Snake 81) (h : Conditions q) : valuation q 1691 = false ∨ valuation q 1714 = false ∨ valuation q 1727 = true := by
  have hs : count1719 q = (countLit q [-92, -93, -95, -97, -98, -101, -104, -105]) + (countLit q [-109, -110, -111, -113, -116, -117, -119, -122]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-92, -93, -95, -97, -98, -101, -104, -105]) (l₂ := [-109, -110, -111, -113, -116, -117, -119, -122])
  have hm := merge_two (literal (valuation q) (1691)) (literal (valuation q) (1714)) (literal (valuation q) (1727)) (countLit q [-92, -93, -95, -97, -98, -101, -104, -105]) (countLit q [-109, -110, -111, -113, -116, -117, -119, -122]) (count1719 q) 5 4 (meaning1691 q) (meaning1714 q) (meaning1727 q) hs
  change valuation q 1691 = false ∨ valuation q 1714 = false ∨ valuation q 1727 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1438 (q : Snake 81) (h : Conditions q) : valuation q 1691 = false ∨ valuation q 1715 = false ∨ valuation q 1728 = true := by
  have hs : count1719 q = (countLit q [-92, -93, -95, -97, -98, -101, -104, -105]) + (countLit q [-109, -110, -111, -113, -116, -117, -119, -122]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-92, -93, -95, -97, -98, -101, -104, -105]) (l₂ := [-109, -110, -111, -113, -116, -117, -119, -122])
  have hm := merge_two (literal (valuation q) (1691)) (literal (valuation q) (1715)) (literal (valuation q) (1728)) (countLit q [-92, -93, -95, -97, -98, -101, -104, -105]) (countLit q [-109, -110, -111, -113, -116, -117, -119, -122]) (count1719 q) 5 5 (meaning1691 q) (meaning1715 q) (meaning1728 q) hs
  change valuation q 1691 = false ∨ valuation q 1715 = false ∨ valuation q 1728 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1439 (q : Snake 81) (h : Conditions q) : valuation q 1692 = false ∨ valuation q 1724 = true := by
  have hs : count1719 q = (countLit q [-92, -93, -95, -97, -98, -101, -104, -105]) + (countLit q [-109, -110, -111, -113, -116, -117, -119, -122]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-92, -93, -95, -97, -98, -101, -104, -105]) (l₂ := [-109, -110, -111, -113, -116, -117, -119, -122])
  have hm := merge_left (literal (valuation q) (1692)) (literal (valuation q) (1724)) (countLit q [-92, -93, -95, -97, -98, -101, -104, -105]) (countLit q [-109, -110, -111, -113, -116, -117, -119, -122]) (count1719 q) 6 (meaning1692 q) (meaning1724 q) hs
  change valuation q 1692 = false ∨ valuation q 1724 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1440 (q : Snake 81) (h : Conditions q) : valuation q 1692 = false ∨ valuation q 1711 = false ∨ valuation q 1725 = true := by
  have hs : count1719 q = (countLit q [-92, -93, -95, -97, -98, -101, -104, -105]) + (countLit q [-109, -110, -111, -113, -116, -117, -119, -122]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-92, -93, -95, -97, -98, -101, -104, -105]) (l₂ := [-109, -110, -111, -113, -116, -117, -119, -122])
  have hm := merge_two (literal (valuation q) (1692)) (literal (valuation q) (1711)) (literal (valuation q) (1725)) (countLit q [-92, -93, -95, -97, -98, -101, -104, -105]) (countLit q [-109, -110, -111, -113, -116, -117, -119, -122]) (count1719 q) 6 1 (meaning1692 q) (meaning1711 q) (meaning1725 q) hs
  change valuation q 1692 = false ∨ valuation q 1711 = false ∨ valuation q 1725 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem block44 (q : Snake 81) (h : Conditions q) : Dfs112FirstBoolean.Block44 (valuation q) :=
  ⟨clause1409 q h, clause1410 q h, clause1411 q h, clause1412 q h, clause1413 q h, clause1414 q h, clause1415 q h, clause1416 q h, clause1417 q h, clause1418 q h, clause1419 q h, clause1420 q h, clause1421 q h, clause1422 q h, clause1423 q h, clause1424 q h, clause1425 q h, clause1426 q h, clause1427 q h, clause1428 q h, clause1429 q h, clause1430 q h, clause1431 q h, clause1432 q h, clause1433 q h, clause1434 q h, clause1435 q h, clause1436 q h, clause1437 q h, clause1438 q h, clause1439 q h, clause1440 q h⟩

end
end Snake9.Regrowth.First112
