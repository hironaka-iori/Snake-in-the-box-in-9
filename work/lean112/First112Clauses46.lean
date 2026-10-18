import First112Semantics
import Dfs112FirstBooleanInputs
namespace Snake9.Regrowth.First112
noncomputable section
local instance blockDec46 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause1473 (q : Snake 81) (h : Conditions q) : valuation q 1660 = false ∨ valuation q 1727 = false ∨ valuation q 1749 = true := by
  have hs : count1735 q = (countLit q [-61, -62, -64, -67, -68, -69, -72, -73, -76, -77, -79, -80, -84, -85, -88, -90]) + (countLit q [-92, -93, -95, -97, -98, -101, -104, -105, -109, -110, -111, -113, -116, -117, -119, -122]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-61, -62, -64, -67, -68, -69, -72, -73, -76, -77, -79, -80, -84, -85, -88, -90]) (l₂ := [-92, -93, -95, -97, -98, -101, -104, -105, -109, -110, -111, -113, -116, -117, -119, -122])
  have hm := merge_two (literal (valuation q) (1660)) (literal (valuation q) (1727)) (literal (valuation q) (1749)) (countLit q [-61, -62, -64, -67, -68, -69, -72, -73, -76, -77, -79, -80, -84, -85, -88, -90]) (countLit q [-92, -93, -95, -97, -98, -101, -104, -105, -109, -110, -111, -113, -116, -117, -119, -122]) (count1735 q) 6 9 (meaning1660 q) (meaning1727 q) (meaning1749 q) hs
  change valuation q 1660 = false ∨ valuation q 1727 = false ∨ valuation q 1749 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1474 (q : Snake 81) (h : Conditions q) : valuation q 1660 = false ∨ valuation q 1728 = false ∨ valuation q 1750 = true := by
  have hs : count1735 q = (countLit q [-61, -62, -64, -67, -68, -69, -72, -73, -76, -77, -79, -80, -84, -85, -88, -90]) + (countLit q [-92, -93, -95, -97, -98, -101, -104, -105, -109, -110, -111, -113, -116, -117, -119, -122]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-61, -62, -64, -67, -68, -69, -72, -73, -76, -77, -79, -80, -84, -85, -88, -90]) (l₂ := [-92, -93, -95, -97, -98, -101, -104, -105, -109, -110, -111, -113, -116, -117, -119, -122])
  have hm := merge_two (literal (valuation q) (1660)) (literal (valuation q) (1728)) (literal (valuation q) (1750)) (countLit q [-61, -62, -64, -67, -68, -69, -72, -73, -76, -77, -79, -80, -84, -85, -88, -90]) (countLit q [-92, -93, -95, -97, -98, -101, -104, -105, -109, -110, -111, -113, -116, -117, -119, -122]) (count1735 q) 6 10 (meaning1660 q) (meaning1728 q) (meaning1750 q) hs
  change valuation q 1660 = false ∨ valuation q 1728 = false ∨ valuation q 1750 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1475 (q : Snake 81) (h : Conditions q) : valuation q 1661 = false ∨ valuation q 1721 = false ∨ valuation q 1744 = true := by
  have hs : count1735 q = (countLit q [-61, -62, -64, -67, -68, -69, -72, -73, -76, -77, -79, -80, -84, -85, -88, -90]) + (countLit q [-92, -93, -95, -97, -98, -101, -104, -105, -109, -110, -111, -113, -116, -117, -119, -122]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-61, -62, -64, -67, -68, -69, -72, -73, -76, -77, -79, -80, -84, -85, -88, -90]) (l₂ := [-92, -93, -95, -97, -98, -101, -104, -105, -109, -110, -111, -113, -116, -117, -119, -122])
  have hm := merge_two (literal (valuation q) (1661)) (literal (valuation q) (1721)) (literal (valuation q) (1744)) (countLit q [-61, -62, -64, -67, -68, -69, -72, -73, -76, -77, -79, -80, -84, -85, -88, -90]) (countLit q [-92, -93, -95, -97, -98, -101, -104, -105, -109, -110, -111, -113, -116, -117, -119, -122]) (count1735 q) 7 3 (meaning1661 q) (meaning1721 q) (meaning1744 q) hs
  change valuation q 1661 = false ∨ valuation q 1721 = false ∨ valuation q 1744 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1476 (q : Snake 81) (h : Conditions q) : valuation q 1661 = false ∨ valuation q 1722 = false ∨ valuation q 1745 = true := by
  have hs : count1735 q = (countLit q [-61, -62, -64, -67, -68, -69, -72, -73, -76, -77, -79, -80, -84, -85, -88, -90]) + (countLit q [-92, -93, -95, -97, -98, -101, -104, -105, -109, -110, -111, -113, -116, -117, -119, -122]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-61, -62, -64, -67, -68, -69, -72, -73, -76, -77, -79, -80, -84, -85, -88, -90]) (l₂ := [-92, -93, -95, -97, -98, -101, -104, -105, -109, -110, -111, -113, -116, -117, -119, -122])
  have hm := merge_two (literal (valuation q) (1661)) (literal (valuation q) (1722)) (literal (valuation q) (1745)) (countLit q [-61, -62, -64, -67, -68, -69, -72, -73, -76, -77, -79, -80, -84, -85, -88, -90]) (countLit q [-92, -93, -95, -97, -98, -101, -104, -105, -109, -110, -111, -113, -116, -117, -119, -122]) (count1735 q) 7 4 (meaning1661 q) (meaning1722 q) (meaning1745 q) hs
  change valuation q 1661 = false ∨ valuation q 1722 = false ∨ valuation q 1745 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1477 (q : Snake 81) (h : Conditions q) : valuation q 1661 = false ∨ valuation q 1723 = false ∨ valuation q 1746 = true := by
  have hs : count1735 q = (countLit q [-61, -62, -64, -67, -68, -69, -72, -73, -76, -77, -79, -80, -84, -85, -88, -90]) + (countLit q [-92, -93, -95, -97, -98, -101, -104, -105, -109, -110, -111, -113, -116, -117, -119, -122]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-61, -62, -64, -67, -68, -69, -72, -73, -76, -77, -79, -80, -84, -85, -88, -90]) (l₂ := [-92, -93, -95, -97, -98, -101, -104, -105, -109, -110, -111, -113, -116, -117, -119, -122])
  have hm := merge_two (literal (valuation q) (1661)) (literal (valuation q) (1723)) (literal (valuation q) (1746)) (countLit q [-61, -62, -64, -67, -68, -69, -72, -73, -76, -77, -79, -80, -84, -85, -88, -90]) (countLit q [-92, -93, -95, -97, -98, -101, -104, -105, -109, -110, -111, -113, -116, -117, -119, -122]) (count1735 q) 7 5 (meaning1661 q) (meaning1723 q) (meaning1746 q) hs
  change valuation q 1661 = false ∨ valuation q 1723 = false ∨ valuation q 1746 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1478 (q : Snake 81) (h : Conditions q) : valuation q 1661 = false ∨ valuation q 1724 = false ∨ valuation q 1747 = true := by
  have hs : count1735 q = (countLit q [-61, -62, -64, -67, -68, -69, -72, -73, -76, -77, -79, -80, -84, -85, -88, -90]) + (countLit q [-92, -93, -95, -97, -98, -101, -104, -105, -109, -110, -111, -113, -116, -117, -119, -122]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-61, -62, -64, -67, -68, -69, -72, -73, -76, -77, -79, -80, -84, -85, -88, -90]) (l₂ := [-92, -93, -95, -97, -98, -101, -104, -105, -109, -110, -111, -113, -116, -117, -119, -122])
  have hm := merge_two (literal (valuation q) (1661)) (literal (valuation q) (1724)) (literal (valuation q) (1747)) (countLit q [-61, -62, -64, -67, -68, -69, -72, -73, -76, -77, -79, -80, -84, -85, -88, -90]) (countLit q [-92, -93, -95, -97, -98, -101, -104, -105, -109, -110, -111, -113, -116, -117, -119, -122]) (count1735 q) 7 6 (meaning1661 q) (meaning1724 q) (meaning1747 q) hs
  change valuation q 1661 = false ∨ valuation q 1724 = false ∨ valuation q 1747 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1479 (q : Snake 81) (h : Conditions q) : valuation q 1661 = false ∨ valuation q 1725 = false ∨ valuation q 1748 = true := by
  have hs : count1735 q = (countLit q [-61, -62, -64, -67, -68, -69, -72, -73, -76, -77, -79, -80, -84, -85, -88, -90]) + (countLit q [-92, -93, -95, -97, -98, -101, -104, -105, -109, -110, -111, -113, -116, -117, -119, -122]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-61, -62, -64, -67, -68, -69, -72, -73, -76, -77, -79, -80, -84, -85, -88, -90]) (l₂ := [-92, -93, -95, -97, -98, -101, -104, -105, -109, -110, -111, -113, -116, -117, -119, -122])
  have hm := merge_two (literal (valuation q) (1661)) (literal (valuation q) (1725)) (literal (valuation q) (1748)) (countLit q [-61, -62, -64, -67, -68, -69, -72, -73, -76, -77, -79, -80, -84, -85, -88, -90]) (countLit q [-92, -93, -95, -97, -98, -101, -104, -105, -109, -110, -111, -113, -116, -117, -119, -122]) (count1735 q) 7 7 (meaning1661 q) (meaning1725 q) (meaning1748 q) hs
  change valuation q 1661 = false ∨ valuation q 1725 = false ∨ valuation q 1748 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1480 (q : Snake 81) (h : Conditions q) : valuation q 1661 = false ∨ valuation q 1726 = false ∨ valuation q 1749 = true := by
  have hs : count1735 q = (countLit q [-61, -62, -64, -67, -68, -69, -72, -73, -76, -77, -79, -80, -84, -85, -88, -90]) + (countLit q [-92, -93, -95, -97, -98, -101, -104, -105, -109, -110, -111, -113, -116, -117, -119, -122]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-61, -62, -64, -67, -68, -69, -72, -73, -76, -77, -79, -80, -84, -85, -88, -90]) (l₂ := [-92, -93, -95, -97, -98, -101, -104, -105, -109, -110, -111, -113, -116, -117, -119, -122])
  have hm := merge_two (literal (valuation q) (1661)) (literal (valuation q) (1726)) (literal (valuation q) (1749)) (countLit q [-61, -62, -64, -67, -68, -69, -72, -73, -76, -77, -79, -80, -84, -85, -88, -90]) (countLit q [-92, -93, -95, -97, -98, -101, -104, -105, -109, -110, -111, -113, -116, -117, -119, -122]) (count1735 q) 7 8 (meaning1661 q) (meaning1726 q) (meaning1749 q) hs
  change valuation q 1661 = false ∨ valuation q 1726 = false ∨ valuation q 1749 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1481 (q : Snake 81) (h : Conditions q) : valuation q 1662 = false ∨ valuation q 1721 = false ∨ valuation q 1745 = true := by
  have hs : count1735 q = (countLit q [-61, -62, -64, -67, -68, -69, -72, -73, -76, -77, -79, -80, -84, -85, -88, -90]) + (countLit q [-92, -93, -95, -97, -98, -101, -104, -105, -109, -110, -111, -113, -116, -117, -119, -122]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-61, -62, -64, -67, -68, -69, -72, -73, -76, -77, -79, -80, -84, -85, -88, -90]) (l₂ := [-92, -93, -95, -97, -98, -101, -104, -105, -109, -110, -111, -113, -116, -117, -119, -122])
  have hm := merge_two (literal (valuation q) (1662)) (literal (valuation q) (1721)) (literal (valuation q) (1745)) (countLit q [-61, -62, -64, -67, -68, -69, -72, -73, -76, -77, -79, -80, -84, -85, -88, -90]) (countLit q [-92, -93, -95, -97, -98, -101, -104, -105, -109, -110, -111, -113, -116, -117, -119, -122]) (count1735 q) 8 3 (meaning1662 q) (meaning1721 q) (meaning1745 q) hs
  change valuation q 1662 = false ∨ valuation q 1721 = false ∨ valuation q 1745 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1482 (q : Snake 81) (h : Conditions q) : valuation q 1662 = false ∨ valuation q 1722 = false ∨ valuation q 1746 = true := by
  have hs : count1735 q = (countLit q [-61, -62, -64, -67, -68, -69, -72, -73, -76, -77, -79, -80, -84, -85, -88, -90]) + (countLit q [-92, -93, -95, -97, -98, -101, -104, -105, -109, -110, -111, -113, -116, -117, -119, -122]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-61, -62, -64, -67, -68, -69, -72, -73, -76, -77, -79, -80, -84, -85, -88, -90]) (l₂ := [-92, -93, -95, -97, -98, -101, -104, -105, -109, -110, -111, -113, -116, -117, -119, -122])
  have hm := merge_two (literal (valuation q) (1662)) (literal (valuation q) (1722)) (literal (valuation q) (1746)) (countLit q [-61, -62, -64, -67, -68, -69, -72, -73, -76, -77, -79, -80, -84, -85, -88, -90]) (countLit q [-92, -93, -95, -97, -98, -101, -104, -105, -109, -110, -111, -113, -116, -117, -119, -122]) (count1735 q) 8 4 (meaning1662 q) (meaning1722 q) (meaning1746 q) hs
  change valuation q 1662 = false ∨ valuation q 1722 = false ∨ valuation q 1746 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1483 (q : Snake 81) (h : Conditions q) : valuation q 1662 = false ∨ valuation q 1723 = false ∨ valuation q 1747 = true := by
  have hs : count1735 q = (countLit q [-61, -62, -64, -67, -68, -69, -72, -73, -76, -77, -79, -80, -84, -85, -88, -90]) + (countLit q [-92, -93, -95, -97, -98, -101, -104, -105, -109, -110, -111, -113, -116, -117, -119, -122]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-61, -62, -64, -67, -68, -69, -72, -73, -76, -77, -79, -80, -84, -85, -88, -90]) (l₂ := [-92, -93, -95, -97, -98, -101, -104, -105, -109, -110, -111, -113, -116, -117, -119, -122])
  have hm := merge_two (literal (valuation q) (1662)) (literal (valuation q) (1723)) (literal (valuation q) (1747)) (countLit q [-61, -62, -64, -67, -68, -69, -72, -73, -76, -77, -79, -80, -84, -85, -88, -90]) (countLit q [-92, -93, -95, -97, -98, -101, -104, -105, -109, -110, -111, -113, -116, -117, -119, -122]) (count1735 q) 8 5 (meaning1662 q) (meaning1723 q) (meaning1747 q) hs
  change valuation q 1662 = false ∨ valuation q 1723 = false ∨ valuation q 1747 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1484 (q : Snake 81) (h : Conditions q) : valuation q 1662 = false ∨ valuation q 1724 = false ∨ valuation q 1748 = true := by
  have hs : count1735 q = (countLit q [-61, -62, -64, -67, -68, -69, -72, -73, -76, -77, -79, -80, -84, -85, -88, -90]) + (countLit q [-92, -93, -95, -97, -98, -101, -104, -105, -109, -110, -111, -113, -116, -117, -119, -122]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-61, -62, -64, -67, -68, -69, -72, -73, -76, -77, -79, -80, -84, -85, -88, -90]) (l₂ := [-92, -93, -95, -97, -98, -101, -104, -105, -109, -110, -111, -113, -116, -117, -119, -122])
  have hm := merge_two (literal (valuation q) (1662)) (literal (valuation q) (1724)) (literal (valuation q) (1748)) (countLit q [-61, -62, -64, -67, -68, -69, -72, -73, -76, -77, -79, -80, -84, -85, -88, -90]) (countLit q [-92, -93, -95, -97, -98, -101, -104, -105, -109, -110, -111, -113, -116, -117, -119, -122]) (count1735 q) 8 6 (meaning1662 q) (meaning1724 q) (meaning1748 q) hs
  change valuation q 1662 = false ∨ valuation q 1724 = false ∨ valuation q 1748 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1485 (q : Snake 81) (h : Conditions q) : valuation q 1662 = false ∨ valuation q 1725 = false ∨ valuation q 1749 = true := by
  have hs : count1735 q = (countLit q [-61, -62, -64, -67, -68, -69, -72, -73, -76, -77, -79, -80, -84, -85, -88, -90]) + (countLit q [-92, -93, -95, -97, -98, -101, -104, -105, -109, -110, -111, -113, -116, -117, -119, -122]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-61, -62, -64, -67, -68, -69, -72, -73, -76, -77, -79, -80, -84, -85, -88, -90]) (l₂ := [-92, -93, -95, -97, -98, -101, -104, -105, -109, -110, -111, -113, -116, -117, -119, -122])
  have hm := merge_two (literal (valuation q) (1662)) (literal (valuation q) (1725)) (literal (valuation q) (1749)) (countLit q [-61, -62, -64, -67, -68, -69, -72, -73, -76, -77, -79, -80, -84, -85, -88, -90]) (countLit q [-92, -93, -95, -97, -98, -101, -104, -105, -109, -110, -111, -113, -116, -117, -119, -122]) (count1735 q) 8 7 (meaning1662 q) (meaning1725 q) (meaning1749 q) hs
  change valuation q 1662 = false ∨ valuation q 1725 = false ∨ valuation q 1749 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1486 (q : Snake 81) (h : Conditions q) : valuation q 1662 = false ∨ valuation q 1726 = false ∨ valuation q 1750 = true := by
  have hs : count1735 q = (countLit q [-61, -62, -64, -67, -68, -69, -72, -73, -76, -77, -79, -80, -84, -85, -88, -90]) + (countLit q [-92, -93, -95, -97, -98, -101, -104, -105, -109, -110, -111, -113, -116, -117, -119, -122]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-61, -62, -64, -67, -68, -69, -72, -73, -76, -77, -79, -80, -84, -85, -88, -90]) (l₂ := [-92, -93, -95, -97, -98, -101, -104, -105, -109, -110, -111, -113, -116, -117, -119, -122])
  have hm := merge_two (literal (valuation q) (1662)) (literal (valuation q) (1726)) (literal (valuation q) (1750)) (countLit q [-61, -62, -64, -67, -68, -69, -72, -73, -76, -77, -79, -80, -84, -85, -88, -90]) (countLit q [-92, -93, -95, -97, -98, -101, -104, -105, -109, -110, -111, -113, -116, -117, -119, -122]) (count1735 q) 8 8 (meaning1662 q) (meaning1726 q) (meaning1750 q) hs
  change valuation q 1662 = false ∨ valuation q 1726 = false ∨ valuation q 1750 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1487 (q : Snake 81) (h : Conditions q) : valuation q 1663 = false ∨ valuation q 1721 = false ∨ valuation q 1746 = true := by
  have hs : count1735 q = (countLit q [-61, -62, -64, -67, -68, -69, -72, -73, -76, -77, -79, -80, -84, -85, -88, -90]) + (countLit q [-92, -93, -95, -97, -98, -101, -104, -105, -109, -110, -111, -113, -116, -117, -119, -122]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-61, -62, -64, -67, -68, -69, -72, -73, -76, -77, -79, -80, -84, -85, -88, -90]) (l₂ := [-92, -93, -95, -97, -98, -101, -104, -105, -109, -110, -111, -113, -116, -117, -119, -122])
  have hm := merge_two (literal (valuation q) (1663)) (literal (valuation q) (1721)) (literal (valuation q) (1746)) (countLit q [-61, -62, -64, -67, -68, -69, -72, -73, -76, -77, -79, -80, -84, -85, -88, -90]) (countLit q [-92, -93, -95, -97, -98, -101, -104, -105, -109, -110, -111, -113, -116, -117, -119, -122]) (count1735 q) 9 3 (meaning1663 q) (meaning1721 q) (meaning1746 q) hs
  change valuation q 1663 = false ∨ valuation q 1721 = false ∨ valuation q 1746 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1488 (q : Snake 81) (h : Conditions q) : valuation q 1663 = false ∨ valuation q 1722 = false ∨ valuation q 1747 = true := by
  have hs : count1735 q = (countLit q [-61, -62, -64, -67, -68, -69, -72, -73, -76, -77, -79, -80, -84, -85, -88, -90]) + (countLit q [-92, -93, -95, -97, -98, -101, -104, -105, -109, -110, -111, -113, -116, -117, -119, -122]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-61, -62, -64, -67, -68, -69, -72, -73, -76, -77, -79, -80, -84, -85, -88, -90]) (l₂ := [-92, -93, -95, -97, -98, -101, -104, -105, -109, -110, -111, -113, -116, -117, -119, -122])
  have hm := merge_two (literal (valuation q) (1663)) (literal (valuation q) (1722)) (literal (valuation q) (1747)) (countLit q [-61, -62, -64, -67, -68, -69, -72, -73, -76, -77, -79, -80, -84, -85, -88, -90]) (countLit q [-92, -93, -95, -97, -98, -101, -104, -105, -109, -110, -111, -113, -116, -117, -119, -122]) (count1735 q) 9 4 (meaning1663 q) (meaning1722 q) (meaning1747 q) hs
  change valuation q 1663 = false ∨ valuation q 1722 = false ∨ valuation q 1747 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1489 (q : Snake 81) (h : Conditions q) : valuation q 1663 = false ∨ valuation q 1723 = false ∨ valuation q 1748 = true := by
  have hs : count1735 q = (countLit q [-61, -62, -64, -67, -68, -69, -72, -73, -76, -77, -79, -80, -84, -85, -88, -90]) + (countLit q [-92, -93, -95, -97, -98, -101, -104, -105, -109, -110, -111, -113, -116, -117, -119, -122]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-61, -62, -64, -67, -68, -69, -72, -73, -76, -77, -79, -80, -84, -85, -88, -90]) (l₂ := [-92, -93, -95, -97, -98, -101, -104, -105, -109, -110, -111, -113, -116, -117, -119, -122])
  have hm := merge_two (literal (valuation q) (1663)) (literal (valuation q) (1723)) (literal (valuation q) (1748)) (countLit q [-61, -62, -64, -67, -68, -69, -72, -73, -76, -77, -79, -80, -84, -85, -88, -90]) (countLit q [-92, -93, -95, -97, -98, -101, -104, -105, -109, -110, -111, -113, -116, -117, -119, -122]) (count1735 q) 9 5 (meaning1663 q) (meaning1723 q) (meaning1748 q) hs
  change valuation q 1663 = false ∨ valuation q 1723 = false ∨ valuation q 1748 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1490 (q : Snake 81) (h : Conditions q) : valuation q 1663 = false ∨ valuation q 1724 = false ∨ valuation q 1749 = true := by
  have hs : count1735 q = (countLit q [-61, -62, -64, -67, -68, -69, -72, -73, -76, -77, -79, -80, -84, -85, -88, -90]) + (countLit q [-92, -93, -95, -97, -98, -101, -104, -105, -109, -110, -111, -113, -116, -117, -119, -122]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-61, -62, -64, -67, -68, -69, -72, -73, -76, -77, -79, -80, -84, -85, -88, -90]) (l₂ := [-92, -93, -95, -97, -98, -101, -104, -105, -109, -110, -111, -113, -116, -117, -119, -122])
  have hm := merge_two (literal (valuation q) (1663)) (literal (valuation q) (1724)) (literal (valuation q) (1749)) (countLit q [-61, -62, -64, -67, -68, -69, -72, -73, -76, -77, -79, -80, -84, -85, -88, -90]) (countLit q [-92, -93, -95, -97, -98, -101, -104, -105, -109, -110, -111, -113, -116, -117, -119, -122]) (count1735 q) 9 6 (meaning1663 q) (meaning1724 q) (meaning1749 q) hs
  change valuation q 1663 = false ∨ valuation q 1724 = false ∨ valuation q 1749 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1491 (q : Snake 81) (h : Conditions q) : valuation q 1663 = false ∨ valuation q 1725 = false ∨ valuation q 1750 = true := by
  have hs : count1735 q = (countLit q [-61, -62, -64, -67, -68, -69, -72, -73, -76, -77, -79, -80, -84, -85, -88, -90]) + (countLit q [-92, -93, -95, -97, -98, -101, -104, -105, -109, -110, -111, -113, -116, -117, -119, -122]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-61, -62, -64, -67, -68, -69, -72, -73, -76, -77, -79, -80, -84, -85, -88, -90]) (l₂ := [-92, -93, -95, -97, -98, -101, -104, -105, -109, -110, -111, -113, -116, -117, -119, -122])
  have hm := merge_two (literal (valuation q) (1663)) (literal (valuation q) (1725)) (literal (valuation q) (1750)) (countLit q [-61, -62, -64, -67, -68, -69, -72, -73, -76, -77, -79, -80, -84, -85, -88, -90]) (countLit q [-92, -93, -95, -97, -98, -101, -104, -105, -109, -110, -111, -113, -116, -117, -119, -122]) (count1735 q) 9 7 (meaning1663 q) (meaning1725 q) (meaning1750 q) hs
  change valuation q 1663 = false ∨ valuation q 1725 = false ∨ valuation q 1750 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1492 (q : Snake 81) (h : Conditions q) : valuation q 1664 = false ∨ valuation q 1721 = false ∨ valuation q 1747 = true := by
  have hs : count1735 q = (countLit q [-61, -62, -64, -67, -68, -69, -72, -73, -76, -77, -79, -80, -84, -85, -88, -90]) + (countLit q [-92, -93, -95, -97, -98, -101, -104, -105, -109, -110, -111, -113, -116, -117, -119, -122]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-61, -62, -64, -67, -68, -69, -72, -73, -76, -77, -79, -80, -84, -85, -88, -90]) (l₂ := [-92, -93, -95, -97, -98, -101, -104, -105, -109, -110, -111, -113, -116, -117, -119, -122])
  have hm := merge_two (literal (valuation q) (1664)) (literal (valuation q) (1721)) (literal (valuation q) (1747)) (countLit q [-61, -62, -64, -67, -68, -69, -72, -73, -76, -77, -79, -80, -84, -85, -88, -90]) (countLit q [-92, -93, -95, -97, -98, -101, -104, -105, -109, -110, -111, -113, -116, -117, -119, -122]) (count1735 q) 10 3 (meaning1664 q) (meaning1721 q) (meaning1747 q) hs
  change valuation q 1664 = false ∨ valuation q 1721 = false ∨ valuation q 1747 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1493 (q : Snake 81) (h : Conditions q) : valuation q 1664 = false ∨ valuation q 1722 = false ∨ valuation q 1748 = true := by
  have hs : count1735 q = (countLit q [-61, -62, -64, -67, -68, -69, -72, -73, -76, -77, -79, -80, -84, -85, -88, -90]) + (countLit q [-92, -93, -95, -97, -98, -101, -104, -105, -109, -110, -111, -113, -116, -117, -119, -122]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-61, -62, -64, -67, -68, -69, -72, -73, -76, -77, -79, -80, -84, -85, -88, -90]) (l₂ := [-92, -93, -95, -97, -98, -101, -104, -105, -109, -110, -111, -113, -116, -117, -119, -122])
  have hm := merge_two (literal (valuation q) (1664)) (literal (valuation q) (1722)) (literal (valuation q) (1748)) (countLit q [-61, -62, -64, -67, -68, -69, -72, -73, -76, -77, -79, -80, -84, -85, -88, -90]) (countLit q [-92, -93, -95, -97, -98, -101, -104, -105, -109, -110, -111, -113, -116, -117, -119, -122]) (count1735 q) 10 4 (meaning1664 q) (meaning1722 q) (meaning1748 q) hs
  change valuation q 1664 = false ∨ valuation q 1722 = false ∨ valuation q 1748 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1494 (q : Snake 81) (h : Conditions q) : valuation q 1664 = false ∨ valuation q 1723 = false ∨ valuation q 1749 = true := by
  have hs : count1735 q = (countLit q [-61, -62, -64, -67, -68, -69, -72, -73, -76, -77, -79, -80, -84, -85, -88, -90]) + (countLit q [-92, -93, -95, -97, -98, -101, -104, -105, -109, -110, -111, -113, -116, -117, -119, -122]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-61, -62, -64, -67, -68, -69, -72, -73, -76, -77, -79, -80, -84, -85, -88, -90]) (l₂ := [-92, -93, -95, -97, -98, -101, -104, -105, -109, -110, -111, -113, -116, -117, -119, -122])
  have hm := merge_two (literal (valuation q) (1664)) (literal (valuation q) (1723)) (literal (valuation q) (1749)) (countLit q [-61, -62, -64, -67, -68, -69, -72, -73, -76, -77, -79, -80, -84, -85, -88, -90]) (countLit q [-92, -93, -95, -97, -98, -101, -104, -105, -109, -110, -111, -113, -116, -117, -119, -122]) (count1735 q) 10 5 (meaning1664 q) (meaning1723 q) (meaning1749 q) hs
  change valuation q 1664 = false ∨ valuation q 1723 = false ∨ valuation q 1749 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1495 (q : Snake 81) (h : Conditions q) : valuation q 1664 = false ∨ valuation q 1724 = false ∨ valuation q 1750 = true := by
  have hs : count1735 q = (countLit q [-61, -62, -64, -67, -68, -69, -72, -73, -76, -77, -79, -80, -84, -85, -88, -90]) + (countLit q [-92, -93, -95, -97, -98, -101, -104, -105, -109, -110, -111, -113, -116, -117, -119, -122]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-61, -62, -64, -67, -68, -69, -72, -73, -76, -77, -79, -80, -84, -85, -88, -90]) (l₂ := [-92, -93, -95, -97, -98, -101, -104, -105, -109, -110, -111, -113, -116, -117, -119, -122])
  have hm := merge_two (literal (valuation q) (1664)) (literal (valuation q) (1724)) (literal (valuation q) (1750)) (countLit q [-61, -62, -64, -67, -68, -69, -72, -73, -76, -77, -79, -80, -84, -85, -88, -90]) (countLit q [-92, -93, -95, -97, -98, -101, -104, -105, -109, -110, -111, -113, -116, -117, -119, -122]) (count1735 q) 10 6 (meaning1664 q) (meaning1724 q) (meaning1750 q) hs
  change valuation q 1664 = false ∨ valuation q 1724 = false ∨ valuation q 1750 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1496 (q : Snake 81) (h : Conditions q) : valuation q 1590 = false ∨ valuation q 1750 = false ∨ valuation q 1780 = true := by
  have hs : count1758 q = (countLit q [-2, -4, -6, -8, -10, -12, -13, -15, -18, -19, -21, -23, -24, -26, -27, -31, -33, -34, -35, -39, -41, -42, -43, -45, -47, -49, -50, -53, -56, -59, -60]) + (countLit q [-61, -62, -64, -67, -68, -69, -72, -73, -76, -77, -79, -80, -84, -85, -88, -90, -92, -93, -95, -97, -98, -101, -104, -105, -109, -110, -111, -113, -116, -117, -119, -122]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-2, -4, -6, -8, -10, -12, -13, -15, -18, -19, -21, -23, -24, -26, -27, -31, -33, -34, -35, -39, -41, -42, -43, -45, -47, -49, -50, -53, -56, -59, -60]) (l₂ := [-61, -62, -64, -67, -68, -69, -72, -73, -76, -77, -79, -80, -84, -85, -88, -90, -92, -93, -95, -97, -98, -101, -104, -105, -109, -110, -111, -113, -116, -117, -119, -122])
  have hm := merge_two (literal (valuation q) (1590)) (literal (valuation q) (1750)) (literal (valuation q) (1780)) (countLit q [-2, -4, -6, -8, -10, -12, -13, -15, -18, -19, -21, -23, -24, -26, -27, -31, -33, -34, -35, -39, -41, -42, -43, -45, -47, -49, -50, -53, -56, -59, -60]) (countLit q [-61, -62, -64, -67, -68, -69, -72, -73, -76, -77, -79, -80, -84, -85, -88, -90, -92, -93, -95, -97, -98, -101, -104, -105, -109, -110, -111, -113, -116, -117, -119, -122]) (count1758 q) 7 16 (meaning1590 q) (meaning1750 q) (meaning1780 q) hs
  change valuation q 1590 = false ∨ valuation q 1750 = false ∨ valuation q 1780 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1497 (q : Snake 81) (h : Conditions q) : valuation q 1591 = false ∨ valuation q 1749 = false ∨ valuation q 1780 = true := by
  have hs : count1758 q = (countLit q [-2, -4, -6, -8, -10, -12, -13, -15, -18, -19, -21, -23, -24, -26, -27, -31, -33, -34, -35, -39, -41, -42, -43, -45, -47, -49, -50, -53, -56, -59, -60]) + (countLit q [-61, -62, -64, -67, -68, -69, -72, -73, -76, -77, -79, -80, -84, -85, -88, -90, -92, -93, -95, -97, -98, -101, -104, -105, -109, -110, -111, -113, -116, -117, -119, -122]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-2, -4, -6, -8, -10, -12, -13, -15, -18, -19, -21, -23, -24, -26, -27, -31, -33, -34, -35, -39, -41, -42, -43, -45, -47, -49, -50, -53, -56, -59, -60]) (l₂ := [-61, -62, -64, -67, -68, -69, -72, -73, -76, -77, -79, -80, -84, -85, -88, -90, -92, -93, -95, -97, -98, -101, -104, -105, -109, -110, -111, -113, -116, -117, -119, -122])
  have hm := merge_two (literal (valuation q) (1591)) (literal (valuation q) (1749)) (literal (valuation q) (1780)) (countLit q [-2, -4, -6, -8, -10, -12, -13, -15, -18, -19, -21, -23, -24, -26, -27, -31, -33, -34, -35, -39, -41, -42, -43, -45, -47, -49, -50, -53, -56, -59, -60]) (countLit q [-61, -62, -64, -67, -68, -69, -72, -73, -76, -77, -79, -80, -84, -85, -88, -90, -92, -93, -95, -97, -98, -101, -104, -105, -109, -110, -111, -113, -116, -117, -119, -122]) (count1758 q) 8 15 (meaning1591 q) (meaning1749 q) (meaning1780 q) hs
  change valuation q 1591 = false ∨ valuation q 1749 = false ∨ valuation q 1780 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1498 (q : Snake 81) (h : Conditions q) : valuation q 1592 = false ∨ valuation q 1748 = false ∨ valuation q 1780 = true := by
  have hs : count1758 q = (countLit q [-2, -4, -6, -8, -10, -12, -13, -15, -18, -19, -21, -23, -24, -26, -27, -31, -33, -34, -35, -39, -41, -42, -43, -45, -47, -49, -50, -53, -56, -59, -60]) + (countLit q [-61, -62, -64, -67, -68, -69, -72, -73, -76, -77, -79, -80, -84, -85, -88, -90, -92, -93, -95, -97, -98, -101, -104, -105, -109, -110, -111, -113, -116, -117, -119, -122]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-2, -4, -6, -8, -10, -12, -13, -15, -18, -19, -21, -23, -24, -26, -27, -31, -33, -34, -35, -39, -41, -42, -43, -45, -47, -49, -50, -53, -56, -59, -60]) (l₂ := [-61, -62, -64, -67, -68, -69, -72, -73, -76, -77, -79, -80, -84, -85, -88, -90, -92, -93, -95, -97, -98, -101, -104, -105, -109, -110, -111, -113, -116, -117, -119, -122])
  have hm := merge_two (literal (valuation q) (1592)) (literal (valuation q) (1748)) (literal (valuation q) (1780)) (countLit q [-2, -4, -6, -8, -10, -12, -13, -15, -18, -19, -21, -23, -24, -26, -27, -31, -33, -34, -35, -39, -41, -42, -43, -45, -47, -49, -50, -53, -56, -59, -60]) (countLit q [-61, -62, -64, -67, -68, -69, -72, -73, -76, -77, -79, -80, -84, -85, -88, -90, -92, -93, -95, -97, -98, -101, -104, -105, -109, -110, -111, -113, -116, -117, -119, -122]) (count1758 q) 9 14 (meaning1592 q) (meaning1748 q) (meaning1780 q) hs
  change valuation q 1592 = false ∨ valuation q 1748 = false ∨ valuation q 1780 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1499 (q : Snake 81) (h : Conditions q) : valuation q 1593 = false ∨ valuation q 1747 = false ∨ valuation q 1780 = true := by
  have hs : count1758 q = (countLit q [-2, -4, -6, -8, -10, -12, -13, -15, -18, -19, -21, -23, -24, -26, -27, -31, -33, -34, -35, -39, -41, -42, -43, -45, -47, -49, -50, -53, -56, -59, -60]) + (countLit q [-61, -62, -64, -67, -68, -69, -72, -73, -76, -77, -79, -80, -84, -85, -88, -90, -92, -93, -95, -97, -98, -101, -104, -105, -109, -110, -111, -113, -116, -117, -119, -122]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-2, -4, -6, -8, -10, -12, -13, -15, -18, -19, -21, -23, -24, -26, -27, -31, -33, -34, -35, -39, -41, -42, -43, -45, -47, -49, -50, -53, -56, -59, -60]) (l₂ := [-61, -62, -64, -67, -68, -69, -72, -73, -76, -77, -79, -80, -84, -85, -88, -90, -92, -93, -95, -97, -98, -101, -104, -105, -109, -110, -111, -113, -116, -117, -119, -122])
  have hm := merge_two (literal (valuation q) (1593)) (literal (valuation q) (1747)) (literal (valuation q) (1780)) (countLit q [-2, -4, -6, -8, -10, -12, -13, -15, -18, -19, -21, -23, -24, -26, -27, -31, -33, -34, -35, -39, -41, -42, -43, -45, -47, -49, -50, -53, -56, -59, -60]) (countLit q [-61, -62, -64, -67, -68, -69, -72, -73, -76, -77, -79, -80, -84, -85, -88, -90, -92, -93, -95, -97, -98, -101, -104, -105, -109, -110, -111, -113, -116, -117, -119, -122]) (count1758 q) 10 13 (meaning1593 q) (meaning1747 q) (meaning1780 q) hs
  change valuation q 1593 = false ∨ valuation q 1747 = false ∨ valuation q 1780 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1500 (q : Snake 81) (h : Conditions q) : valuation q 1594 = false ∨ valuation q 1746 = false ∨ valuation q 1780 = true := by
  have hs : count1758 q = (countLit q [-2, -4, -6, -8, -10, -12, -13, -15, -18, -19, -21, -23, -24, -26, -27, -31, -33, -34, -35, -39, -41, -42, -43, -45, -47, -49, -50, -53, -56, -59, -60]) + (countLit q [-61, -62, -64, -67, -68, -69, -72, -73, -76, -77, -79, -80, -84, -85, -88, -90, -92, -93, -95, -97, -98, -101, -104, -105, -109, -110, -111, -113, -116, -117, -119, -122]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-2, -4, -6, -8, -10, -12, -13, -15, -18, -19, -21, -23, -24, -26, -27, -31, -33, -34, -35, -39, -41, -42, -43, -45, -47, -49, -50, -53, -56, -59, -60]) (l₂ := [-61, -62, -64, -67, -68, -69, -72, -73, -76, -77, -79, -80, -84, -85, -88, -90, -92, -93, -95, -97, -98, -101, -104, -105, -109, -110, -111, -113, -116, -117, -119, -122])
  have hm := merge_two (literal (valuation q) (1594)) (literal (valuation q) (1746)) (literal (valuation q) (1780)) (countLit q [-2, -4, -6, -8, -10, -12, -13, -15, -18, -19, -21, -23, -24, -26, -27, -31, -33, -34, -35, -39, -41, -42, -43, -45, -47, -49, -50, -53, -56, -59, -60]) (countLit q [-61, -62, -64, -67, -68, -69, -72, -73, -76, -77, -79, -80, -84, -85, -88, -90, -92, -93, -95, -97, -98, -101, -104, -105, -109, -110, -111, -113, -116, -117, -119, -122]) (count1758 q) 11 12 (meaning1594 q) (meaning1746 q) (meaning1780 q) hs
  change valuation q 1594 = false ∨ valuation q 1746 = false ∨ valuation q 1780 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1501 (q : Snake 81) (h : Conditions q) : valuation q 1595 = false ∨ valuation q 1745 = false ∨ valuation q 1780 = true := by
  have hs : count1758 q = (countLit q [-2, -4, -6, -8, -10, -12, -13, -15, -18, -19, -21, -23, -24, -26, -27, -31, -33, -34, -35, -39, -41, -42, -43, -45, -47, -49, -50, -53, -56, -59, -60]) + (countLit q [-61, -62, -64, -67, -68, -69, -72, -73, -76, -77, -79, -80, -84, -85, -88, -90, -92, -93, -95, -97, -98, -101, -104, -105, -109, -110, -111, -113, -116, -117, -119, -122]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-2, -4, -6, -8, -10, -12, -13, -15, -18, -19, -21, -23, -24, -26, -27, -31, -33, -34, -35, -39, -41, -42, -43, -45, -47, -49, -50, -53, -56, -59, -60]) (l₂ := [-61, -62, -64, -67, -68, -69, -72, -73, -76, -77, -79, -80, -84, -85, -88, -90, -92, -93, -95, -97, -98, -101, -104, -105, -109, -110, -111, -113, -116, -117, -119, -122])
  have hm := merge_two (literal (valuation q) (1595)) (literal (valuation q) (1745)) (literal (valuation q) (1780)) (countLit q [-2, -4, -6, -8, -10, -12, -13, -15, -18, -19, -21, -23, -24, -26, -27, -31, -33, -34, -35, -39, -41, -42, -43, -45, -47, -49, -50, -53, -56, -59, -60]) (countLit q [-61, -62, -64, -67, -68, -69, -72, -73, -76, -77, -79, -80, -84, -85, -88, -90, -92, -93, -95, -97, -98, -101, -104, -105, -109, -110, -111, -113, -116, -117, -119, -122]) (count1758 q) 12 11 (meaning1595 q) (meaning1745 q) (meaning1780 q) hs
  change valuation q 1595 = false ∨ valuation q 1745 = false ∨ valuation q 1780 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1502 (q : Snake 81) (h : Conditions q) : valuation q 1596 = false ∨ valuation q 1744 = false ∨ valuation q 1780 = true := by
  have hs : count1758 q = (countLit q [-2, -4, -6, -8, -10, -12, -13, -15, -18, -19, -21, -23, -24, -26, -27, -31, -33, -34, -35, -39, -41, -42, -43, -45, -47, -49, -50, -53, -56, -59, -60]) + (countLit q [-61, -62, -64, -67, -68, -69, -72, -73, -76, -77, -79, -80, -84, -85, -88, -90, -92, -93, -95, -97, -98, -101, -104, -105, -109, -110, -111, -113, -116, -117, -119, -122]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-2, -4, -6, -8, -10, -12, -13, -15, -18, -19, -21, -23, -24, -26, -27, -31, -33, -34, -35, -39, -41, -42, -43, -45, -47, -49, -50, -53, -56, -59, -60]) (l₂ := [-61, -62, -64, -67, -68, -69, -72, -73, -76, -77, -79, -80, -84, -85, -88, -90, -92, -93, -95, -97, -98, -101, -104, -105, -109, -110, -111, -113, -116, -117, -119, -122])
  have hm := merge_two (literal (valuation q) (1596)) (literal (valuation q) (1744)) (literal (valuation q) (1780)) (countLit q [-2, -4, -6, -8, -10, -12, -13, -15, -18, -19, -21, -23, -24, -26, -27, -31, -33, -34, -35, -39, -41, -42, -43, -45, -47, -49, -50, -53, -56, -59, -60]) (countLit q [-61, -62, -64, -67, -68, -69, -72, -73, -76, -77, -79, -80, -84, -85, -88, -90, -92, -93, -95, -97, -98, -101, -104, -105, -109, -110, -111, -113, -116, -117, -119, -122]) (count1758 q) 13 10 (meaning1596 q) (meaning1744 q) (meaning1780 q) hs
  change valuation q 1596 = false ∨ valuation q 1744 = false ∨ valuation q 1780 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1503 (q : Snake 81) (h : Conditions q) : valuation q 1597 = false ∨ valuation q 1743 = false ∨ valuation q 1780 = true := by
  have hs : count1758 q = (countLit q [-2, -4, -6, -8, -10, -12, -13, -15, -18, -19, -21, -23, -24, -26, -27, -31, -33, -34, -35, -39, -41, -42, -43, -45, -47, -49, -50, -53, -56, -59, -60]) + (countLit q [-61, -62, -64, -67, -68, -69, -72, -73, -76, -77, -79, -80, -84, -85, -88, -90, -92, -93, -95, -97, -98, -101, -104, -105, -109, -110, -111, -113, -116, -117, -119, -122]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-2, -4, -6, -8, -10, -12, -13, -15, -18, -19, -21, -23, -24, -26, -27, -31, -33, -34, -35, -39, -41, -42, -43, -45, -47, -49, -50, -53, -56, -59, -60]) (l₂ := [-61, -62, -64, -67, -68, -69, -72, -73, -76, -77, -79, -80, -84, -85, -88, -90, -92, -93, -95, -97, -98, -101, -104, -105, -109, -110, -111, -113, -116, -117, -119, -122])
  have hm := merge_two (literal (valuation q) (1597)) (literal (valuation q) (1743)) (literal (valuation q) (1780)) (countLit q [-2, -4, -6, -8, -10, -12, -13, -15, -18, -19, -21, -23, -24, -26, -27, -31, -33, -34, -35, -39, -41, -42, -43, -45, -47, -49, -50, -53, -56, -59, -60]) (countLit q [-61, -62, -64, -67, -68, -69, -72, -73, -76, -77, -79, -80, -84, -85, -88, -90, -92, -93, -95, -97, -98, -101, -104, -105, -109, -110, -111, -113, -116, -117, -119, -122]) (count1758 q) 14 9 (meaning1597 q) (meaning1743 q) (meaning1780 q) hs
  change valuation q 1597 = false ∨ valuation q 1743 = false ∨ valuation q 1780 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1504 (q : Snake 81) (h : Conditions q) : valuation q 1780 = false := by
  rw [value1780]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have he : count1758 q = (oddSide.filter (fun v => !(decide (InPath q v)))).length := by
    rw [← List.countP_eq_length_filter]
    rfl
  have hb := absent_odd_bound q h
  rw [he]
  omega

theorem block46 (q : Snake 81) (h : Conditions q) : Dfs112FirstBoolean.Block46 (valuation q) :=
  ⟨clause1473 q h, clause1474 q h, clause1475 q h, clause1476 q h, clause1477 q h, clause1478 q h, clause1479 q h, clause1480 q h, clause1481 q h, clause1482 q h, clause1483 q h, clause1484 q h, clause1485 q h, clause1486 q h, clause1487 q h, clause1488 q h, clause1489 q h, clause1490 q h, clause1491 q h, clause1492 q h, clause1493 q h, clause1494 q h, clause1495 q h, clause1496 q h, clause1497 q h, clause1498 q h, clause1499 q h, clause1500 q h, clause1501 q h, clause1502 q h, clause1503 q h, clause1504 q h⟩

end
end Snake9.Regrowth.First112
