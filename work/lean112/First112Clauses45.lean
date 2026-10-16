import First112Semantics
import Dfs112FirstBooleanInputs
namespace Snake9.Regrowth.First112
noncomputable section
local instance blockDec45 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause1441 (q : Snake 81) (h : Conditions q) : valuation q 1692 = false ∨ valuation q 1712 = false ∨ valuation q 1726 = true := by
  have hs : count1719 q = (countLit q [-92, -93, -95, -97, -98, -101, -104, -105]) + (countLit q [-109, -110, -111, -113, -116, -117, -119, -122]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-92, -93, -95, -97, -98, -101, -104, -105]) (l₂ := [-109, -110, -111, -113, -116, -117, -119, -122])
  have hm := merge_two (literal (valuation q) (1692)) (literal (valuation q) (1712)) (literal (valuation q) (1726)) (countLit q [-92, -93, -95, -97, -98, -101, -104, -105]) (countLit q [-109, -110, -111, -113, -116, -117, -119, -122]) (count1719 q) 6 2 (meaning1692 q) (meaning1712 q) (meaning1726 q) hs
  change valuation q 1692 = false ∨ valuation q 1712 = false ∨ valuation q 1726 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1442 (q : Snake 81) (h : Conditions q) : valuation q 1692 = false ∨ valuation q 1713 = false ∨ valuation q 1727 = true := by
  have hs : count1719 q = (countLit q [-92, -93, -95, -97, -98, -101, -104, -105]) + (countLit q [-109, -110, -111, -113, -116, -117, -119, -122]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-92, -93, -95, -97, -98, -101, -104, -105]) (l₂ := [-109, -110, -111, -113, -116, -117, -119, -122])
  have hm := merge_two (literal (valuation q) (1692)) (literal (valuation q) (1713)) (literal (valuation q) (1727)) (countLit q [-92, -93, -95, -97, -98, -101, -104, -105]) (countLit q [-109, -110, -111, -113, -116, -117, -119, -122]) (count1719 q) 6 3 (meaning1692 q) (meaning1713 q) (meaning1727 q) hs
  change valuation q 1692 = false ∨ valuation q 1713 = false ∨ valuation q 1727 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1443 (q : Snake 81) (h : Conditions q) : valuation q 1692 = false ∨ valuation q 1714 = false ∨ valuation q 1728 = true := by
  have hs : count1719 q = (countLit q [-92, -93, -95, -97, -98, -101, -104, -105]) + (countLit q [-109, -110, -111, -113, -116, -117, -119, -122]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-92, -93, -95, -97, -98, -101, -104, -105]) (l₂ := [-109, -110, -111, -113, -116, -117, -119, -122])
  have hm := merge_two (literal (valuation q) (1692)) (literal (valuation q) (1714)) (literal (valuation q) (1728)) (countLit q [-92, -93, -95, -97, -98, -101, -104, -105]) (countLit q [-109, -110, -111, -113, -116, -117, -119, -122]) (count1719 q) 6 4 (meaning1692 q) (meaning1714 q) (meaning1728 q) hs
  change valuation q 1692 = false ∨ valuation q 1714 = false ∨ valuation q 1728 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1444 (q : Snake 81) (h : Conditions q) : valuation q 1693 = false ∨ valuation q 1711 = false ∨ valuation q 1726 = true := by
  have hs : count1719 q = (countLit q [-92, -93, -95, -97, -98, -101, -104, -105]) + (countLit q [-109, -110, -111, -113, -116, -117, -119, -122]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-92, -93, -95, -97, -98, -101, -104, -105]) (l₂ := [-109, -110, -111, -113, -116, -117, -119, -122])
  have hm := merge_two (literal (valuation q) (1693)) (literal (valuation q) (1711)) (literal (valuation q) (1726)) (countLit q [-92, -93, -95, -97, -98, -101, -104, -105]) (countLit q [-109, -110, -111, -113, -116, -117, -119, -122]) (count1719 q) 7 1 (meaning1693 q) (meaning1711 q) (meaning1726 q) hs
  change valuation q 1693 = false ∨ valuation q 1711 = false ∨ valuation q 1726 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1445 (q : Snake 81) (h : Conditions q) : valuation q 1693 = false ∨ valuation q 1712 = false ∨ valuation q 1727 = true := by
  have hs : count1719 q = (countLit q [-92, -93, -95, -97, -98, -101, -104, -105]) + (countLit q [-109, -110, -111, -113, -116, -117, -119, -122]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-92, -93, -95, -97, -98, -101, -104, -105]) (l₂ := [-109, -110, -111, -113, -116, -117, -119, -122])
  have hm := merge_two (literal (valuation q) (1693)) (literal (valuation q) (1712)) (literal (valuation q) (1727)) (countLit q [-92, -93, -95, -97, -98, -101, -104, -105]) (countLit q [-109, -110, -111, -113, -116, -117, -119, -122]) (count1719 q) 7 2 (meaning1693 q) (meaning1712 q) (meaning1727 q) hs
  change valuation q 1693 = false ∨ valuation q 1712 = false ∨ valuation q 1727 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1446 (q : Snake 81) (h : Conditions q) : valuation q 1693 = false ∨ valuation q 1713 = false ∨ valuation q 1728 = true := by
  have hs : count1719 q = (countLit q [-92, -93, -95, -97, -98, -101, -104, -105]) + (countLit q [-109, -110, -111, -113, -116, -117, -119, -122]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-92, -93, -95, -97, -98, -101, -104, -105]) (l₂ := [-109, -110, -111, -113, -116, -117, -119, -122])
  have hm := merge_two (literal (valuation q) (1693)) (literal (valuation q) (1713)) (literal (valuation q) (1728)) (countLit q [-92, -93, -95, -97, -98, -101, -104, -105]) (countLit q [-109, -110, -111, -113, -116, -117, -119, -122]) (count1719 q) 7 3 (meaning1693 q) (meaning1713 q) (meaning1728 q) hs
  change valuation q 1693 = false ∨ valuation q 1713 = false ∨ valuation q 1728 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1447 (q : Snake 81) (h : Conditions q) : valuation q 1656 = false ∨ valuation q 1725 = false ∨ valuation q 1743 = true := by
  have hs : count1735 q = (countLit q [-61, -62, -64, -67, -68, -69, -72, -73, -76, -77, -79, -80, -84, -85, -88, -90]) + (countLit q [-92, -93, -95, -97, -98, -101, -104, -105, -109, -110, -111, -113, -116, -117, -119, -122]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-61, -62, -64, -67, -68, -69, -72, -73, -76, -77, -79, -80, -84, -85, -88, -90]) (l₂ := [-92, -93, -95, -97, -98, -101, -104, -105, -109, -110, -111, -113, -116, -117, -119, -122])
  have hm := merge_two (literal (valuation q) (1656)) (literal (valuation q) (1725)) (literal (valuation q) (1743)) (countLit q [-61, -62, -64, -67, -68, -69, -72, -73, -76, -77, -79, -80, -84, -85, -88, -90]) (countLit q [-92, -93, -95, -97, -98, -101, -104, -105, -109, -110, -111, -113, -116, -117, -119, -122]) (count1735 q) 2 7 (meaning1656 q) (meaning1725 q) (meaning1743 q) hs
  change valuation q 1656 = false ∨ valuation q 1725 = false ∨ valuation q 1743 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1448 (q : Snake 81) (h : Conditions q) : valuation q 1656 = false ∨ valuation q 1726 = false ∨ valuation q 1744 = true := by
  have hs : count1735 q = (countLit q [-61, -62, -64, -67, -68, -69, -72, -73, -76, -77, -79, -80, -84, -85, -88, -90]) + (countLit q [-92, -93, -95, -97, -98, -101, -104, -105, -109, -110, -111, -113, -116, -117, -119, -122]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-61, -62, -64, -67, -68, -69, -72, -73, -76, -77, -79, -80, -84, -85, -88, -90]) (l₂ := [-92, -93, -95, -97, -98, -101, -104, -105, -109, -110, -111, -113, -116, -117, -119, -122])
  have hm := merge_two (literal (valuation q) (1656)) (literal (valuation q) (1726)) (literal (valuation q) (1744)) (countLit q [-61, -62, -64, -67, -68, -69, -72, -73, -76, -77, -79, -80, -84, -85, -88, -90]) (countLit q [-92, -93, -95, -97, -98, -101, -104, -105, -109, -110, -111, -113, -116, -117, -119, -122]) (count1735 q) 2 8 (meaning1656 q) (meaning1726 q) (meaning1744 q) hs
  change valuation q 1656 = false ∨ valuation q 1726 = false ∨ valuation q 1744 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1449 (q : Snake 81) (h : Conditions q) : valuation q 1656 = false ∨ valuation q 1727 = false ∨ valuation q 1745 = true := by
  have hs : count1735 q = (countLit q [-61, -62, -64, -67, -68, -69, -72, -73, -76, -77, -79, -80, -84, -85, -88, -90]) + (countLit q [-92, -93, -95, -97, -98, -101, -104, -105, -109, -110, -111, -113, -116, -117, -119, -122]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-61, -62, -64, -67, -68, -69, -72, -73, -76, -77, -79, -80, -84, -85, -88, -90]) (l₂ := [-92, -93, -95, -97, -98, -101, -104, -105, -109, -110, -111, -113, -116, -117, -119, -122])
  have hm := merge_two (literal (valuation q) (1656)) (literal (valuation q) (1727)) (literal (valuation q) (1745)) (countLit q [-61, -62, -64, -67, -68, -69, -72, -73, -76, -77, -79, -80, -84, -85, -88, -90]) (countLit q [-92, -93, -95, -97, -98, -101, -104, -105, -109, -110, -111, -113, -116, -117, -119, -122]) (count1735 q) 2 9 (meaning1656 q) (meaning1727 q) (meaning1745 q) hs
  change valuation q 1656 = false ∨ valuation q 1727 = false ∨ valuation q 1745 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1450 (q : Snake 81) (h : Conditions q) : valuation q 1657 = false ∨ valuation q 1724 = false ∨ valuation q 1743 = true := by
  have hs : count1735 q = (countLit q [-61, -62, -64, -67, -68, -69, -72, -73, -76, -77, -79, -80, -84, -85, -88, -90]) + (countLit q [-92, -93, -95, -97, -98, -101, -104, -105, -109, -110, -111, -113, -116, -117, -119, -122]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-61, -62, -64, -67, -68, -69, -72, -73, -76, -77, -79, -80, -84, -85, -88, -90]) (l₂ := [-92, -93, -95, -97, -98, -101, -104, -105, -109, -110, -111, -113, -116, -117, -119, -122])
  have hm := merge_two (literal (valuation q) (1657)) (literal (valuation q) (1724)) (literal (valuation q) (1743)) (countLit q [-61, -62, -64, -67, -68, -69, -72, -73, -76, -77, -79, -80, -84, -85, -88, -90]) (countLit q [-92, -93, -95, -97, -98, -101, -104, -105, -109, -110, -111, -113, -116, -117, -119, -122]) (count1735 q) 3 6 (meaning1657 q) (meaning1724 q) (meaning1743 q) hs
  change valuation q 1657 = false ∨ valuation q 1724 = false ∨ valuation q 1743 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1451 (q : Snake 81) (h : Conditions q) : valuation q 1657 = false ∨ valuation q 1725 = false ∨ valuation q 1744 = true := by
  have hs : count1735 q = (countLit q [-61, -62, -64, -67, -68, -69, -72, -73, -76, -77, -79, -80, -84, -85, -88, -90]) + (countLit q [-92, -93, -95, -97, -98, -101, -104, -105, -109, -110, -111, -113, -116, -117, -119, -122]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-61, -62, -64, -67, -68, -69, -72, -73, -76, -77, -79, -80, -84, -85, -88, -90]) (l₂ := [-92, -93, -95, -97, -98, -101, -104, -105, -109, -110, -111, -113, -116, -117, -119, -122])
  have hm := merge_two (literal (valuation q) (1657)) (literal (valuation q) (1725)) (literal (valuation q) (1744)) (countLit q [-61, -62, -64, -67, -68, -69, -72, -73, -76, -77, -79, -80, -84, -85, -88, -90]) (countLit q [-92, -93, -95, -97, -98, -101, -104, -105, -109, -110, -111, -113, -116, -117, -119, -122]) (count1735 q) 3 7 (meaning1657 q) (meaning1725 q) (meaning1744 q) hs
  change valuation q 1657 = false ∨ valuation q 1725 = false ∨ valuation q 1744 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1452 (q : Snake 81) (h : Conditions q) : valuation q 1657 = false ∨ valuation q 1726 = false ∨ valuation q 1745 = true := by
  have hs : count1735 q = (countLit q [-61, -62, -64, -67, -68, -69, -72, -73, -76, -77, -79, -80, -84, -85, -88, -90]) + (countLit q [-92, -93, -95, -97, -98, -101, -104, -105, -109, -110, -111, -113, -116, -117, -119, -122]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-61, -62, -64, -67, -68, -69, -72, -73, -76, -77, -79, -80, -84, -85, -88, -90]) (l₂ := [-92, -93, -95, -97, -98, -101, -104, -105, -109, -110, -111, -113, -116, -117, -119, -122])
  have hm := merge_two (literal (valuation q) (1657)) (literal (valuation q) (1726)) (literal (valuation q) (1745)) (countLit q [-61, -62, -64, -67, -68, -69, -72, -73, -76, -77, -79, -80, -84, -85, -88, -90]) (countLit q [-92, -93, -95, -97, -98, -101, -104, -105, -109, -110, -111, -113, -116, -117, -119, -122]) (count1735 q) 3 8 (meaning1657 q) (meaning1726 q) (meaning1745 q) hs
  change valuation q 1657 = false ∨ valuation q 1726 = false ∨ valuation q 1745 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1453 (q : Snake 81) (h : Conditions q) : valuation q 1657 = false ∨ valuation q 1727 = false ∨ valuation q 1746 = true := by
  have hs : count1735 q = (countLit q [-61, -62, -64, -67, -68, -69, -72, -73, -76, -77, -79, -80, -84, -85, -88, -90]) + (countLit q [-92, -93, -95, -97, -98, -101, -104, -105, -109, -110, -111, -113, -116, -117, -119, -122]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-61, -62, -64, -67, -68, -69, -72, -73, -76, -77, -79, -80, -84, -85, -88, -90]) (l₂ := [-92, -93, -95, -97, -98, -101, -104, -105, -109, -110, -111, -113, -116, -117, -119, -122])
  have hm := merge_two (literal (valuation q) (1657)) (literal (valuation q) (1727)) (literal (valuation q) (1746)) (countLit q [-61, -62, -64, -67, -68, -69, -72, -73, -76, -77, -79, -80, -84, -85, -88, -90]) (countLit q [-92, -93, -95, -97, -98, -101, -104, -105, -109, -110, -111, -113, -116, -117, -119, -122]) (count1735 q) 3 9 (meaning1657 q) (meaning1727 q) (meaning1746 q) hs
  change valuation q 1657 = false ∨ valuation q 1727 = false ∨ valuation q 1746 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1454 (q : Snake 81) (h : Conditions q) : valuation q 1657 = false ∨ valuation q 1728 = false ∨ valuation q 1747 = true := by
  have hs : count1735 q = (countLit q [-61, -62, -64, -67, -68, -69, -72, -73, -76, -77, -79, -80, -84, -85, -88, -90]) + (countLit q [-92, -93, -95, -97, -98, -101, -104, -105, -109, -110, -111, -113, -116, -117, -119, -122]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-61, -62, -64, -67, -68, -69, -72, -73, -76, -77, -79, -80, -84, -85, -88, -90]) (l₂ := [-92, -93, -95, -97, -98, -101, -104, -105, -109, -110, -111, -113, -116, -117, -119, -122])
  have hm := merge_two (literal (valuation q) (1657)) (literal (valuation q) (1728)) (literal (valuation q) (1747)) (countLit q [-61, -62, -64, -67, -68, -69, -72, -73, -76, -77, -79, -80, -84, -85, -88, -90]) (countLit q [-92, -93, -95, -97, -98, -101, -104, -105, -109, -110, -111, -113, -116, -117, -119, -122]) (count1735 q) 3 10 (meaning1657 q) (meaning1728 q) (meaning1747 q) hs
  change valuation q 1657 = false ∨ valuation q 1728 = false ∨ valuation q 1747 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1455 (q : Snake 81) (h : Conditions q) : valuation q 1658 = false ∨ valuation q 1723 = false ∨ valuation q 1743 = true := by
  have hs : count1735 q = (countLit q [-61, -62, -64, -67, -68, -69, -72, -73, -76, -77, -79, -80, -84, -85, -88, -90]) + (countLit q [-92, -93, -95, -97, -98, -101, -104, -105, -109, -110, -111, -113, -116, -117, -119, -122]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-61, -62, -64, -67, -68, -69, -72, -73, -76, -77, -79, -80, -84, -85, -88, -90]) (l₂ := [-92, -93, -95, -97, -98, -101, -104, -105, -109, -110, -111, -113, -116, -117, -119, -122])
  have hm := merge_two (literal (valuation q) (1658)) (literal (valuation q) (1723)) (literal (valuation q) (1743)) (countLit q [-61, -62, -64, -67, -68, -69, -72, -73, -76, -77, -79, -80, -84, -85, -88, -90]) (countLit q [-92, -93, -95, -97, -98, -101, -104, -105, -109, -110, -111, -113, -116, -117, -119, -122]) (count1735 q) 4 5 (meaning1658 q) (meaning1723 q) (meaning1743 q) hs
  change valuation q 1658 = false ∨ valuation q 1723 = false ∨ valuation q 1743 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1456 (q : Snake 81) (h : Conditions q) : valuation q 1658 = false ∨ valuation q 1724 = false ∨ valuation q 1744 = true := by
  have hs : count1735 q = (countLit q [-61, -62, -64, -67, -68, -69, -72, -73, -76, -77, -79, -80, -84, -85, -88, -90]) + (countLit q [-92, -93, -95, -97, -98, -101, -104, -105, -109, -110, -111, -113, -116, -117, -119, -122]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-61, -62, -64, -67, -68, -69, -72, -73, -76, -77, -79, -80, -84, -85, -88, -90]) (l₂ := [-92, -93, -95, -97, -98, -101, -104, -105, -109, -110, -111, -113, -116, -117, -119, -122])
  have hm := merge_two (literal (valuation q) (1658)) (literal (valuation q) (1724)) (literal (valuation q) (1744)) (countLit q [-61, -62, -64, -67, -68, -69, -72, -73, -76, -77, -79, -80, -84, -85, -88, -90]) (countLit q [-92, -93, -95, -97, -98, -101, -104, -105, -109, -110, -111, -113, -116, -117, -119, -122]) (count1735 q) 4 6 (meaning1658 q) (meaning1724 q) (meaning1744 q) hs
  change valuation q 1658 = false ∨ valuation q 1724 = false ∨ valuation q 1744 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1457 (q : Snake 81) (h : Conditions q) : valuation q 1658 = false ∨ valuation q 1725 = false ∨ valuation q 1745 = true := by
  have hs : count1735 q = (countLit q [-61, -62, -64, -67, -68, -69, -72, -73, -76, -77, -79, -80, -84, -85, -88, -90]) + (countLit q [-92, -93, -95, -97, -98, -101, -104, -105, -109, -110, -111, -113, -116, -117, -119, -122]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-61, -62, -64, -67, -68, -69, -72, -73, -76, -77, -79, -80, -84, -85, -88, -90]) (l₂ := [-92, -93, -95, -97, -98, -101, -104, -105, -109, -110, -111, -113, -116, -117, -119, -122])
  have hm := merge_two (literal (valuation q) (1658)) (literal (valuation q) (1725)) (literal (valuation q) (1745)) (countLit q [-61, -62, -64, -67, -68, -69, -72, -73, -76, -77, -79, -80, -84, -85, -88, -90]) (countLit q [-92, -93, -95, -97, -98, -101, -104, -105, -109, -110, -111, -113, -116, -117, -119, -122]) (count1735 q) 4 7 (meaning1658 q) (meaning1725 q) (meaning1745 q) hs
  change valuation q 1658 = false ∨ valuation q 1725 = false ∨ valuation q 1745 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1458 (q : Snake 81) (h : Conditions q) : valuation q 1658 = false ∨ valuation q 1726 = false ∨ valuation q 1746 = true := by
  have hs : count1735 q = (countLit q [-61, -62, -64, -67, -68, -69, -72, -73, -76, -77, -79, -80, -84, -85, -88, -90]) + (countLit q [-92, -93, -95, -97, -98, -101, -104, -105, -109, -110, -111, -113, -116, -117, -119, -122]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-61, -62, -64, -67, -68, -69, -72, -73, -76, -77, -79, -80, -84, -85, -88, -90]) (l₂ := [-92, -93, -95, -97, -98, -101, -104, -105, -109, -110, -111, -113, -116, -117, -119, -122])
  have hm := merge_two (literal (valuation q) (1658)) (literal (valuation q) (1726)) (literal (valuation q) (1746)) (countLit q [-61, -62, -64, -67, -68, -69, -72, -73, -76, -77, -79, -80, -84, -85, -88, -90]) (countLit q [-92, -93, -95, -97, -98, -101, -104, -105, -109, -110, -111, -113, -116, -117, -119, -122]) (count1735 q) 4 8 (meaning1658 q) (meaning1726 q) (meaning1746 q) hs
  change valuation q 1658 = false ∨ valuation q 1726 = false ∨ valuation q 1746 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1459 (q : Snake 81) (h : Conditions q) : valuation q 1658 = false ∨ valuation q 1727 = false ∨ valuation q 1747 = true := by
  have hs : count1735 q = (countLit q [-61, -62, -64, -67, -68, -69, -72, -73, -76, -77, -79, -80, -84, -85, -88, -90]) + (countLit q [-92, -93, -95, -97, -98, -101, -104, -105, -109, -110, -111, -113, -116, -117, -119, -122]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-61, -62, -64, -67, -68, -69, -72, -73, -76, -77, -79, -80, -84, -85, -88, -90]) (l₂ := [-92, -93, -95, -97, -98, -101, -104, -105, -109, -110, -111, -113, -116, -117, -119, -122])
  have hm := merge_two (literal (valuation q) (1658)) (literal (valuation q) (1727)) (literal (valuation q) (1747)) (countLit q [-61, -62, -64, -67, -68, -69, -72, -73, -76, -77, -79, -80, -84, -85, -88, -90]) (countLit q [-92, -93, -95, -97, -98, -101, -104, -105, -109, -110, -111, -113, -116, -117, -119, -122]) (count1735 q) 4 9 (meaning1658 q) (meaning1727 q) (meaning1747 q) hs
  change valuation q 1658 = false ∨ valuation q 1727 = false ∨ valuation q 1747 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1460 (q : Snake 81) (h : Conditions q) : valuation q 1658 = false ∨ valuation q 1728 = false ∨ valuation q 1748 = true := by
  have hs : count1735 q = (countLit q [-61, -62, -64, -67, -68, -69, -72, -73, -76, -77, -79, -80, -84, -85, -88, -90]) + (countLit q [-92, -93, -95, -97, -98, -101, -104, -105, -109, -110, -111, -113, -116, -117, -119, -122]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-61, -62, -64, -67, -68, -69, -72, -73, -76, -77, -79, -80, -84, -85, -88, -90]) (l₂ := [-92, -93, -95, -97, -98, -101, -104, -105, -109, -110, -111, -113, -116, -117, -119, -122])
  have hm := merge_two (literal (valuation q) (1658)) (literal (valuation q) (1728)) (literal (valuation q) (1748)) (countLit q [-61, -62, -64, -67, -68, -69, -72, -73, -76, -77, -79, -80, -84, -85, -88, -90]) (countLit q [-92, -93, -95, -97, -98, -101, -104, -105, -109, -110, -111, -113, -116, -117, -119, -122]) (count1735 q) 4 10 (meaning1658 q) (meaning1728 q) (meaning1748 q) hs
  change valuation q 1658 = false ∨ valuation q 1728 = false ∨ valuation q 1748 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1461 (q : Snake 81) (h : Conditions q) : valuation q 1659 = false ∨ valuation q 1722 = false ∨ valuation q 1743 = true := by
  have hs : count1735 q = (countLit q [-61, -62, -64, -67, -68, -69, -72, -73, -76, -77, -79, -80, -84, -85, -88, -90]) + (countLit q [-92, -93, -95, -97, -98, -101, -104, -105, -109, -110, -111, -113, -116, -117, -119, -122]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-61, -62, -64, -67, -68, -69, -72, -73, -76, -77, -79, -80, -84, -85, -88, -90]) (l₂ := [-92, -93, -95, -97, -98, -101, -104, -105, -109, -110, -111, -113, -116, -117, -119, -122])
  have hm := merge_two (literal (valuation q) (1659)) (literal (valuation q) (1722)) (literal (valuation q) (1743)) (countLit q [-61, -62, -64, -67, -68, -69, -72, -73, -76, -77, -79, -80, -84, -85, -88, -90]) (countLit q [-92, -93, -95, -97, -98, -101, -104, -105, -109, -110, -111, -113, -116, -117, -119, -122]) (count1735 q) 5 4 (meaning1659 q) (meaning1722 q) (meaning1743 q) hs
  change valuation q 1659 = false ∨ valuation q 1722 = false ∨ valuation q 1743 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1462 (q : Snake 81) (h : Conditions q) : valuation q 1659 = false ∨ valuation q 1723 = false ∨ valuation q 1744 = true := by
  have hs : count1735 q = (countLit q [-61, -62, -64, -67, -68, -69, -72, -73, -76, -77, -79, -80, -84, -85, -88, -90]) + (countLit q [-92, -93, -95, -97, -98, -101, -104, -105, -109, -110, -111, -113, -116, -117, -119, -122]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-61, -62, -64, -67, -68, -69, -72, -73, -76, -77, -79, -80, -84, -85, -88, -90]) (l₂ := [-92, -93, -95, -97, -98, -101, -104, -105, -109, -110, -111, -113, -116, -117, -119, -122])
  have hm := merge_two (literal (valuation q) (1659)) (literal (valuation q) (1723)) (literal (valuation q) (1744)) (countLit q [-61, -62, -64, -67, -68, -69, -72, -73, -76, -77, -79, -80, -84, -85, -88, -90]) (countLit q [-92, -93, -95, -97, -98, -101, -104, -105, -109, -110, -111, -113, -116, -117, -119, -122]) (count1735 q) 5 5 (meaning1659 q) (meaning1723 q) (meaning1744 q) hs
  change valuation q 1659 = false ∨ valuation q 1723 = false ∨ valuation q 1744 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1463 (q : Snake 81) (h : Conditions q) : valuation q 1659 = false ∨ valuation q 1724 = false ∨ valuation q 1745 = true := by
  have hs : count1735 q = (countLit q [-61, -62, -64, -67, -68, -69, -72, -73, -76, -77, -79, -80, -84, -85, -88, -90]) + (countLit q [-92, -93, -95, -97, -98, -101, -104, -105, -109, -110, -111, -113, -116, -117, -119, -122]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-61, -62, -64, -67, -68, -69, -72, -73, -76, -77, -79, -80, -84, -85, -88, -90]) (l₂ := [-92, -93, -95, -97, -98, -101, -104, -105, -109, -110, -111, -113, -116, -117, -119, -122])
  have hm := merge_two (literal (valuation q) (1659)) (literal (valuation q) (1724)) (literal (valuation q) (1745)) (countLit q [-61, -62, -64, -67, -68, -69, -72, -73, -76, -77, -79, -80, -84, -85, -88, -90]) (countLit q [-92, -93, -95, -97, -98, -101, -104, -105, -109, -110, -111, -113, -116, -117, -119, -122]) (count1735 q) 5 6 (meaning1659 q) (meaning1724 q) (meaning1745 q) hs
  change valuation q 1659 = false ∨ valuation q 1724 = false ∨ valuation q 1745 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1464 (q : Snake 81) (h : Conditions q) : valuation q 1659 = false ∨ valuation q 1725 = false ∨ valuation q 1746 = true := by
  have hs : count1735 q = (countLit q [-61, -62, -64, -67, -68, -69, -72, -73, -76, -77, -79, -80, -84, -85, -88, -90]) + (countLit q [-92, -93, -95, -97, -98, -101, -104, -105, -109, -110, -111, -113, -116, -117, -119, -122]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-61, -62, -64, -67, -68, -69, -72, -73, -76, -77, -79, -80, -84, -85, -88, -90]) (l₂ := [-92, -93, -95, -97, -98, -101, -104, -105, -109, -110, -111, -113, -116, -117, -119, -122])
  have hm := merge_two (literal (valuation q) (1659)) (literal (valuation q) (1725)) (literal (valuation q) (1746)) (countLit q [-61, -62, -64, -67, -68, -69, -72, -73, -76, -77, -79, -80, -84, -85, -88, -90]) (countLit q [-92, -93, -95, -97, -98, -101, -104, -105, -109, -110, -111, -113, -116, -117, -119, -122]) (count1735 q) 5 7 (meaning1659 q) (meaning1725 q) (meaning1746 q) hs
  change valuation q 1659 = false ∨ valuation q 1725 = false ∨ valuation q 1746 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1465 (q : Snake 81) (h : Conditions q) : valuation q 1659 = false ∨ valuation q 1726 = false ∨ valuation q 1747 = true := by
  have hs : count1735 q = (countLit q [-61, -62, -64, -67, -68, -69, -72, -73, -76, -77, -79, -80, -84, -85, -88, -90]) + (countLit q [-92, -93, -95, -97, -98, -101, -104, -105, -109, -110, -111, -113, -116, -117, -119, -122]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-61, -62, -64, -67, -68, -69, -72, -73, -76, -77, -79, -80, -84, -85, -88, -90]) (l₂ := [-92, -93, -95, -97, -98, -101, -104, -105, -109, -110, -111, -113, -116, -117, -119, -122])
  have hm := merge_two (literal (valuation q) (1659)) (literal (valuation q) (1726)) (literal (valuation q) (1747)) (countLit q [-61, -62, -64, -67, -68, -69, -72, -73, -76, -77, -79, -80, -84, -85, -88, -90]) (countLit q [-92, -93, -95, -97, -98, -101, -104, -105, -109, -110, -111, -113, -116, -117, -119, -122]) (count1735 q) 5 8 (meaning1659 q) (meaning1726 q) (meaning1747 q) hs
  change valuation q 1659 = false ∨ valuation q 1726 = false ∨ valuation q 1747 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1466 (q : Snake 81) (h : Conditions q) : valuation q 1659 = false ∨ valuation q 1727 = false ∨ valuation q 1748 = true := by
  have hs : count1735 q = (countLit q [-61, -62, -64, -67, -68, -69, -72, -73, -76, -77, -79, -80, -84, -85, -88, -90]) + (countLit q [-92, -93, -95, -97, -98, -101, -104, -105, -109, -110, -111, -113, -116, -117, -119, -122]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-61, -62, -64, -67, -68, -69, -72, -73, -76, -77, -79, -80, -84, -85, -88, -90]) (l₂ := [-92, -93, -95, -97, -98, -101, -104, -105, -109, -110, -111, -113, -116, -117, -119, -122])
  have hm := merge_two (literal (valuation q) (1659)) (literal (valuation q) (1727)) (literal (valuation q) (1748)) (countLit q [-61, -62, -64, -67, -68, -69, -72, -73, -76, -77, -79, -80, -84, -85, -88, -90]) (countLit q [-92, -93, -95, -97, -98, -101, -104, -105, -109, -110, -111, -113, -116, -117, -119, -122]) (count1735 q) 5 9 (meaning1659 q) (meaning1727 q) (meaning1748 q) hs
  change valuation q 1659 = false ∨ valuation q 1727 = false ∨ valuation q 1748 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1467 (q : Snake 81) (h : Conditions q) : valuation q 1659 = false ∨ valuation q 1728 = false ∨ valuation q 1749 = true := by
  have hs : count1735 q = (countLit q [-61, -62, -64, -67, -68, -69, -72, -73, -76, -77, -79, -80, -84, -85, -88, -90]) + (countLit q [-92, -93, -95, -97, -98, -101, -104, -105, -109, -110, -111, -113, -116, -117, -119, -122]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-61, -62, -64, -67, -68, -69, -72, -73, -76, -77, -79, -80, -84, -85, -88, -90]) (l₂ := [-92, -93, -95, -97, -98, -101, -104, -105, -109, -110, -111, -113, -116, -117, -119, -122])
  have hm := merge_two (literal (valuation q) (1659)) (literal (valuation q) (1728)) (literal (valuation q) (1749)) (countLit q [-61, -62, -64, -67, -68, -69, -72, -73, -76, -77, -79, -80, -84, -85, -88, -90]) (countLit q [-92, -93, -95, -97, -98, -101, -104, -105, -109, -110, -111, -113, -116, -117, -119, -122]) (count1735 q) 5 10 (meaning1659 q) (meaning1728 q) (meaning1749 q) hs
  change valuation q 1659 = false ∨ valuation q 1728 = false ∨ valuation q 1749 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1468 (q : Snake 81) (h : Conditions q) : valuation q 1660 = false ∨ valuation q 1722 = false ∨ valuation q 1744 = true := by
  have hs : count1735 q = (countLit q [-61, -62, -64, -67, -68, -69, -72, -73, -76, -77, -79, -80, -84, -85, -88, -90]) + (countLit q [-92, -93, -95, -97, -98, -101, -104, -105, -109, -110, -111, -113, -116, -117, -119, -122]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-61, -62, -64, -67, -68, -69, -72, -73, -76, -77, -79, -80, -84, -85, -88, -90]) (l₂ := [-92, -93, -95, -97, -98, -101, -104, -105, -109, -110, -111, -113, -116, -117, -119, -122])
  have hm := merge_two (literal (valuation q) (1660)) (literal (valuation q) (1722)) (literal (valuation q) (1744)) (countLit q [-61, -62, -64, -67, -68, -69, -72, -73, -76, -77, -79, -80, -84, -85, -88, -90]) (countLit q [-92, -93, -95, -97, -98, -101, -104, -105, -109, -110, -111, -113, -116, -117, -119, -122]) (count1735 q) 6 4 (meaning1660 q) (meaning1722 q) (meaning1744 q) hs
  change valuation q 1660 = false ∨ valuation q 1722 = false ∨ valuation q 1744 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1469 (q : Snake 81) (h : Conditions q) : valuation q 1660 = false ∨ valuation q 1723 = false ∨ valuation q 1745 = true := by
  have hs : count1735 q = (countLit q [-61, -62, -64, -67, -68, -69, -72, -73, -76, -77, -79, -80, -84, -85, -88, -90]) + (countLit q [-92, -93, -95, -97, -98, -101, -104, -105, -109, -110, -111, -113, -116, -117, -119, -122]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-61, -62, -64, -67, -68, -69, -72, -73, -76, -77, -79, -80, -84, -85, -88, -90]) (l₂ := [-92, -93, -95, -97, -98, -101, -104, -105, -109, -110, -111, -113, -116, -117, -119, -122])
  have hm := merge_two (literal (valuation q) (1660)) (literal (valuation q) (1723)) (literal (valuation q) (1745)) (countLit q [-61, -62, -64, -67, -68, -69, -72, -73, -76, -77, -79, -80, -84, -85, -88, -90]) (countLit q [-92, -93, -95, -97, -98, -101, -104, -105, -109, -110, -111, -113, -116, -117, -119, -122]) (count1735 q) 6 5 (meaning1660 q) (meaning1723 q) (meaning1745 q) hs
  change valuation q 1660 = false ∨ valuation q 1723 = false ∨ valuation q 1745 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1470 (q : Snake 81) (h : Conditions q) : valuation q 1660 = false ∨ valuation q 1724 = false ∨ valuation q 1746 = true := by
  have hs : count1735 q = (countLit q [-61, -62, -64, -67, -68, -69, -72, -73, -76, -77, -79, -80, -84, -85, -88, -90]) + (countLit q [-92, -93, -95, -97, -98, -101, -104, -105, -109, -110, -111, -113, -116, -117, -119, -122]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-61, -62, -64, -67, -68, -69, -72, -73, -76, -77, -79, -80, -84, -85, -88, -90]) (l₂ := [-92, -93, -95, -97, -98, -101, -104, -105, -109, -110, -111, -113, -116, -117, -119, -122])
  have hm := merge_two (literal (valuation q) (1660)) (literal (valuation q) (1724)) (literal (valuation q) (1746)) (countLit q [-61, -62, -64, -67, -68, -69, -72, -73, -76, -77, -79, -80, -84, -85, -88, -90]) (countLit q [-92, -93, -95, -97, -98, -101, -104, -105, -109, -110, -111, -113, -116, -117, -119, -122]) (count1735 q) 6 6 (meaning1660 q) (meaning1724 q) (meaning1746 q) hs
  change valuation q 1660 = false ∨ valuation q 1724 = false ∨ valuation q 1746 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1471 (q : Snake 81) (h : Conditions q) : valuation q 1660 = false ∨ valuation q 1725 = false ∨ valuation q 1747 = true := by
  have hs : count1735 q = (countLit q [-61, -62, -64, -67, -68, -69, -72, -73, -76, -77, -79, -80, -84, -85, -88, -90]) + (countLit q [-92, -93, -95, -97, -98, -101, -104, -105, -109, -110, -111, -113, -116, -117, -119, -122]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-61, -62, -64, -67, -68, -69, -72, -73, -76, -77, -79, -80, -84, -85, -88, -90]) (l₂ := [-92, -93, -95, -97, -98, -101, -104, -105, -109, -110, -111, -113, -116, -117, -119, -122])
  have hm := merge_two (literal (valuation q) (1660)) (literal (valuation q) (1725)) (literal (valuation q) (1747)) (countLit q [-61, -62, -64, -67, -68, -69, -72, -73, -76, -77, -79, -80, -84, -85, -88, -90]) (countLit q [-92, -93, -95, -97, -98, -101, -104, -105, -109, -110, -111, -113, -116, -117, -119, -122]) (count1735 q) 6 7 (meaning1660 q) (meaning1725 q) (meaning1747 q) hs
  change valuation q 1660 = false ∨ valuation q 1725 = false ∨ valuation q 1747 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1472 (q : Snake 81) (h : Conditions q) : valuation q 1660 = false ∨ valuation q 1726 = false ∨ valuation q 1748 = true := by
  have hs : count1735 q = (countLit q [-61, -62, -64, -67, -68, -69, -72, -73, -76, -77, -79, -80, -84, -85, -88, -90]) + (countLit q [-92, -93, -95, -97, -98, -101, -104, -105, -109, -110, -111, -113, -116, -117, -119, -122]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-61, -62, -64, -67, -68, -69, -72, -73, -76, -77, -79, -80, -84, -85, -88, -90]) (l₂ := [-92, -93, -95, -97, -98, -101, -104, -105, -109, -110, -111, -113, -116, -117, -119, -122])
  have hm := merge_two (literal (valuation q) (1660)) (literal (valuation q) (1726)) (literal (valuation q) (1748)) (countLit q [-61, -62, -64, -67, -68, -69, -72, -73, -76, -77, -79, -80, -84, -85, -88, -90]) (countLit q [-92, -93, -95, -97, -98, -101, -104, -105, -109, -110, -111, -113, -116, -117, -119, -122]) (count1735 q) 6 8 (meaning1660 q) (meaning1726 q) (meaning1748 q) hs
  change valuation q 1660 = false ∨ valuation q 1726 = false ∨ valuation q 1748 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem block45 (q : Snake 81) (h : Conditions q) : Dfs112FirstBoolean.Block45 (valuation q) :=
  ⟨clause1441 q h, clause1442 q h, clause1443 q h, clause1444 q h, clause1445 q h, clause1446 q h, clause1447 q h, clause1448 q h, clause1449 q h, clause1450 q h, clause1451 q h, clause1452 q h, clause1453 q h, clause1454 q h, clause1455 q h, clause1456 q h, clause1457 q h, clause1458 q h, clause1459 q h, clause1460 q h, clause1461 q h, clause1462 q h, clause1463 q h, clause1464 q h, clause1465 q h, clause1466 q h, clause1467 q h, clause1468 q h, clause1469 q h, clause1470 q h, clause1471 q h, clause1472 q h⟩

end
end Snake9.Regrowth.First112
