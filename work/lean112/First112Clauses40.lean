import First112Semantics
import Dfs112FirstBooleanInputs
namespace Snake9.Regrowth.First112
noncomputable section
local instance blockDec40 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause1281 (q : Snake 81) (h : Conditions q) : valuation q 1623 = false ∨ valuation q 1648 = false ∨ valuation q 1657 = true := by
  have hs : count1655 q = (countLit q [-61, -62, -64, -67, -68, -69, -72, -73]) + (countLit q [-76, -77, -79, -80, -84, -85, -88, -90]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-61, -62, -64, -67, -68, -69, -72, -73]) (l₂ := [-76, -77, -79, -80, -84, -85, -88, -90])
  have hm := merge_two (literal (valuation q) (1623)) (literal (valuation q) (1648)) (literal (valuation q) (1657)) (countLit q [-61, -62, -64, -67, -68, -69, -72, -73]) (countLit q [-76, -77, -79, -80, -84, -85, -88, -90]) (count1655 q) 1 2 (meaning1623 q) (meaning1648 q) (meaning1657 q) hs
  change valuation q 1623 = false ∨ valuation q 1648 = false ∨ valuation q 1657 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1282 (q : Snake 81) (h : Conditions q) : valuation q 1623 = false ∨ valuation q 1649 = false ∨ valuation q 1658 = true := by
  have hs : count1655 q = (countLit q [-61, -62, -64, -67, -68, -69, -72, -73]) + (countLit q [-76, -77, -79, -80, -84, -85, -88, -90]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-61, -62, -64, -67, -68, -69, -72, -73]) (l₂ := [-76, -77, -79, -80, -84, -85, -88, -90])
  have hm := merge_two (literal (valuation q) (1623)) (literal (valuation q) (1649)) (literal (valuation q) (1658)) (countLit q [-61, -62, -64, -67, -68, -69, -72, -73]) (countLit q [-76, -77, -79, -80, -84, -85, -88, -90]) (count1655 q) 1 3 (meaning1623 q) (meaning1649 q) (meaning1658 q) hs
  change valuation q 1623 = false ∨ valuation q 1649 = false ∨ valuation q 1658 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1283 (q : Snake 81) (h : Conditions q) : valuation q 1623 = false ∨ valuation q 1650 = false ∨ valuation q 1659 = true := by
  have hs : count1655 q = (countLit q [-61, -62, -64, -67, -68, -69, -72, -73]) + (countLit q [-76, -77, -79, -80, -84, -85, -88, -90]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-61, -62, -64, -67, -68, -69, -72, -73]) (l₂ := [-76, -77, -79, -80, -84, -85, -88, -90])
  have hm := merge_two (literal (valuation q) (1623)) (literal (valuation q) (1650)) (literal (valuation q) (1659)) (countLit q [-61, -62, -64, -67, -68, -69, -72, -73]) (countLit q [-76, -77, -79, -80, -84, -85, -88, -90]) (count1655 q) 1 4 (meaning1623 q) (meaning1650 q) (meaning1659 q) hs
  change valuation q 1623 = false ∨ valuation q 1650 = false ∨ valuation q 1659 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1284 (q : Snake 81) (h : Conditions q) : valuation q 1623 = false ∨ valuation q 1651 = false ∨ valuation q 1660 = true := by
  have hs : count1655 q = (countLit q [-61, -62, -64, -67, -68, -69, -72, -73]) + (countLit q [-76, -77, -79, -80, -84, -85, -88, -90]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-61, -62, -64, -67, -68, -69, -72, -73]) (l₂ := [-76, -77, -79, -80, -84, -85, -88, -90])
  have hm := merge_two (literal (valuation q) (1623)) (literal (valuation q) (1651)) (literal (valuation q) (1660)) (countLit q [-61, -62, -64, -67, -68, -69, -72, -73]) (countLit q [-76, -77, -79, -80, -84, -85, -88, -90]) (count1655 q) 1 5 (meaning1623 q) (meaning1651 q) (meaning1660 q) hs
  change valuation q 1623 = false ∨ valuation q 1651 = false ∨ valuation q 1660 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1285 (q : Snake 81) (h : Conditions q) : valuation q 1623 = false ∨ valuation q 1652 = false ∨ valuation q 1661 = true := by
  have hs : count1655 q = (countLit q [-61, -62, -64, -67, -68, -69, -72, -73]) + (countLit q [-76, -77, -79, -80, -84, -85, -88, -90]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-61, -62, -64, -67, -68, -69, -72, -73]) (l₂ := [-76, -77, -79, -80, -84, -85, -88, -90])
  have hm := merge_two (literal (valuation q) (1623)) (literal (valuation q) (1652)) (literal (valuation q) (1661)) (countLit q [-61, -62, -64, -67, -68, -69, -72, -73]) (countLit q [-76, -77, -79, -80, -84, -85, -88, -90]) (count1655 q) 1 6 (meaning1623 q) (meaning1652 q) (meaning1661 q) hs
  change valuation q 1623 = false ∨ valuation q 1652 = false ∨ valuation q 1661 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1286 (q : Snake 81) (h : Conditions q) : valuation q 1624 = false ∨ valuation q 1647 = false ∨ valuation q 1657 = true := by
  have hs : count1655 q = (countLit q [-61, -62, -64, -67, -68, -69, -72, -73]) + (countLit q [-76, -77, -79, -80, -84, -85, -88, -90]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-61, -62, -64, -67, -68, -69, -72, -73]) (l₂ := [-76, -77, -79, -80, -84, -85, -88, -90])
  have hm := merge_two (literal (valuation q) (1624)) (literal (valuation q) (1647)) (literal (valuation q) (1657)) (countLit q [-61, -62, -64, -67, -68, -69, -72, -73]) (countLit q [-76, -77, -79, -80, -84, -85, -88, -90]) (count1655 q) 2 1 (meaning1624 q) (meaning1647 q) (meaning1657 q) hs
  change valuation q 1624 = false ∨ valuation q 1647 = false ∨ valuation q 1657 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1287 (q : Snake 81) (h : Conditions q) : valuation q 1624 = false ∨ valuation q 1648 = false ∨ valuation q 1658 = true := by
  have hs : count1655 q = (countLit q [-61, -62, -64, -67, -68, -69, -72, -73]) + (countLit q [-76, -77, -79, -80, -84, -85, -88, -90]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-61, -62, -64, -67, -68, -69, -72, -73]) (l₂ := [-76, -77, -79, -80, -84, -85, -88, -90])
  have hm := merge_two (literal (valuation q) (1624)) (literal (valuation q) (1648)) (literal (valuation q) (1658)) (countLit q [-61, -62, -64, -67, -68, -69, -72, -73]) (countLit q [-76, -77, -79, -80, -84, -85, -88, -90]) (count1655 q) 2 2 (meaning1624 q) (meaning1648 q) (meaning1658 q) hs
  change valuation q 1624 = false ∨ valuation q 1648 = false ∨ valuation q 1658 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1288 (q : Snake 81) (h : Conditions q) : valuation q 1624 = false ∨ valuation q 1649 = false ∨ valuation q 1659 = true := by
  have hs : count1655 q = (countLit q [-61, -62, -64, -67, -68, -69, -72, -73]) + (countLit q [-76, -77, -79, -80, -84, -85, -88, -90]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-61, -62, -64, -67, -68, -69, -72, -73]) (l₂ := [-76, -77, -79, -80, -84, -85, -88, -90])
  have hm := merge_two (literal (valuation q) (1624)) (literal (valuation q) (1649)) (literal (valuation q) (1659)) (countLit q [-61, -62, -64, -67, -68, -69, -72, -73]) (countLit q [-76, -77, -79, -80, -84, -85, -88, -90]) (count1655 q) 2 3 (meaning1624 q) (meaning1649 q) (meaning1659 q) hs
  change valuation q 1624 = false ∨ valuation q 1649 = false ∨ valuation q 1659 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1289 (q : Snake 81) (h : Conditions q) : valuation q 1624 = false ∨ valuation q 1650 = false ∨ valuation q 1660 = true := by
  have hs : count1655 q = (countLit q [-61, -62, -64, -67, -68, -69, -72, -73]) + (countLit q [-76, -77, -79, -80, -84, -85, -88, -90]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-61, -62, -64, -67, -68, -69, -72, -73]) (l₂ := [-76, -77, -79, -80, -84, -85, -88, -90])
  have hm := merge_two (literal (valuation q) (1624)) (literal (valuation q) (1650)) (literal (valuation q) (1660)) (countLit q [-61, -62, -64, -67, -68, -69, -72, -73]) (countLit q [-76, -77, -79, -80, -84, -85, -88, -90]) (count1655 q) 2 4 (meaning1624 q) (meaning1650 q) (meaning1660 q) hs
  change valuation q 1624 = false ∨ valuation q 1650 = false ∨ valuation q 1660 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1290 (q : Snake 81) (h : Conditions q) : valuation q 1624 = false ∨ valuation q 1651 = false ∨ valuation q 1661 = true := by
  have hs : count1655 q = (countLit q [-61, -62, -64, -67, -68, -69, -72, -73]) + (countLit q [-76, -77, -79, -80, -84, -85, -88, -90]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-61, -62, -64, -67, -68, -69, -72, -73]) (l₂ := [-76, -77, -79, -80, -84, -85, -88, -90])
  have hm := merge_two (literal (valuation q) (1624)) (literal (valuation q) (1651)) (literal (valuation q) (1661)) (countLit q [-61, -62, -64, -67, -68, -69, -72, -73]) (countLit q [-76, -77, -79, -80, -84, -85, -88, -90]) (count1655 q) 2 5 (meaning1624 q) (meaning1651 q) (meaning1661 q) hs
  change valuation q 1624 = false ∨ valuation q 1651 = false ∨ valuation q 1661 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1291 (q : Snake 81) (h : Conditions q) : valuation q 1624 = false ∨ valuation q 1652 = false ∨ valuation q 1662 = true := by
  have hs : count1655 q = (countLit q [-61, -62, -64, -67, -68, -69, -72, -73]) + (countLit q [-76, -77, -79, -80, -84, -85, -88, -90]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-61, -62, -64, -67, -68, -69, -72, -73]) (l₂ := [-76, -77, -79, -80, -84, -85, -88, -90])
  have hm := merge_two (literal (valuation q) (1624)) (literal (valuation q) (1652)) (literal (valuation q) (1662)) (countLit q [-61, -62, -64, -67, -68, -69, -72, -73]) (countLit q [-76, -77, -79, -80, -84, -85, -88, -90]) (count1655 q) 2 6 (meaning1624 q) (meaning1652 q) (meaning1662 q) hs
  change valuation q 1624 = false ∨ valuation q 1652 = false ∨ valuation q 1662 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1292 (q : Snake 81) (h : Conditions q) : valuation q 1624 = false ∨ valuation q 1653 = false ∨ valuation q 1663 = true := by
  have hs : count1655 q = (countLit q [-61, -62, -64, -67, -68, -69, -72, -73]) + (countLit q [-76, -77, -79, -80, -84, -85, -88, -90]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-61, -62, -64, -67, -68, -69, -72, -73]) (l₂ := [-76, -77, -79, -80, -84, -85, -88, -90])
  have hm := merge_two (literal (valuation q) (1624)) (literal (valuation q) (1653)) (literal (valuation q) (1663)) (countLit q [-61, -62, -64, -67, -68, -69, -72, -73]) (countLit q [-76, -77, -79, -80, -84, -85, -88, -90]) (count1655 q) 2 7 (meaning1624 q) (meaning1653 q) (meaning1663 q) hs
  change valuation q 1624 = false ∨ valuation q 1653 = false ∨ valuation q 1663 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1293 (q : Snake 81) (h : Conditions q) : valuation q 1625 = false ∨ valuation q 1647 = false ∨ valuation q 1658 = true := by
  have hs : count1655 q = (countLit q [-61, -62, -64, -67, -68, -69, -72, -73]) + (countLit q [-76, -77, -79, -80, -84, -85, -88, -90]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-61, -62, -64, -67, -68, -69, -72, -73]) (l₂ := [-76, -77, -79, -80, -84, -85, -88, -90])
  have hm := merge_two (literal (valuation q) (1625)) (literal (valuation q) (1647)) (literal (valuation q) (1658)) (countLit q [-61, -62, -64, -67, -68, -69, -72, -73]) (countLit q [-76, -77, -79, -80, -84, -85, -88, -90]) (count1655 q) 3 1 (meaning1625 q) (meaning1647 q) (meaning1658 q) hs
  change valuation q 1625 = false ∨ valuation q 1647 = false ∨ valuation q 1658 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1294 (q : Snake 81) (h : Conditions q) : valuation q 1625 = false ∨ valuation q 1648 = false ∨ valuation q 1659 = true := by
  have hs : count1655 q = (countLit q [-61, -62, -64, -67, -68, -69, -72, -73]) + (countLit q [-76, -77, -79, -80, -84, -85, -88, -90]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-61, -62, -64, -67, -68, -69, -72, -73]) (l₂ := [-76, -77, -79, -80, -84, -85, -88, -90])
  have hm := merge_two (literal (valuation q) (1625)) (literal (valuation q) (1648)) (literal (valuation q) (1659)) (countLit q [-61, -62, -64, -67, -68, -69, -72, -73]) (countLit q [-76, -77, -79, -80, -84, -85, -88, -90]) (count1655 q) 3 2 (meaning1625 q) (meaning1648 q) (meaning1659 q) hs
  change valuation q 1625 = false ∨ valuation q 1648 = false ∨ valuation q 1659 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1295 (q : Snake 81) (h : Conditions q) : valuation q 1625 = false ∨ valuation q 1649 = false ∨ valuation q 1660 = true := by
  have hs : count1655 q = (countLit q [-61, -62, -64, -67, -68, -69, -72, -73]) + (countLit q [-76, -77, -79, -80, -84, -85, -88, -90]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-61, -62, -64, -67, -68, -69, -72, -73]) (l₂ := [-76, -77, -79, -80, -84, -85, -88, -90])
  have hm := merge_two (literal (valuation q) (1625)) (literal (valuation q) (1649)) (literal (valuation q) (1660)) (countLit q [-61, -62, -64, -67, -68, -69, -72, -73]) (countLit q [-76, -77, -79, -80, -84, -85, -88, -90]) (count1655 q) 3 3 (meaning1625 q) (meaning1649 q) (meaning1660 q) hs
  change valuation q 1625 = false ∨ valuation q 1649 = false ∨ valuation q 1660 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1296 (q : Snake 81) (h : Conditions q) : valuation q 1625 = false ∨ valuation q 1650 = false ∨ valuation q 1661 = true := by
  have hs : count1655 q = (countLit q [-61, -62, -64, -67, -68, -69, -72, -73]) + (countLit q [-76, -77, -79, -80, -84, -85, -88, -90]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-61, -62, -64, -67, -68, -69, -72, -73]) (l₂ := [-76, -77, -79, -80, -84, -85, -88, -90])
  have hm := merge_two (literal (valuation q) (1625)) (literal (valuation q) (1650)) (literal (valuation q) (1661)) (countLit q [-61, -62, -64, -67, -68, -69, -72, -73]) (countLit q [-76, -77, -79, -80, -84, -85, -88, -90]) (count1655 q) 3 4 (meaning1625 q) (meaning1650 q) (meaning1661 q) hs
  change valuation q 1625 = false ∨ valuation q 1650 = false ∨ valuation q 1661 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1297 (q : Snake 81) (h : Conditions q) : valuation q 1625 = false ∨ valuation q 1651 = false ∨ valuation q 1662 = true := by
  have hs : count1655 q = (countLit q [-61, -62, -64, -67, -68, -69, -72, -73]) + (countLit q [-76, -77, -79, -80, -84, -85, -88, -90]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-61, -62, -64, -67, -68, -69, -72, -73]) (l₂ := [-76, -77, -79, -80, -84, -85, -88, -90])
  have hm := merge_two (literal (valuation q) (1625)) (literal (valuation q) (1651)) (literal (valuation q) (1662)) (countLit q [-61, -62, -64, -67, -68, -69, -72, -73]) (countLit q [-76, -77, -79, -80, -84, -85, -88, -90]) (count1655 q) 3 5 (meaning1625 q) (meaning1651 q) (meaning1662 q) hs
  change valuation q 1625 = false ∨ valuation q 1651 = false ∨ valuation q 1662 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1298 (q : Snake 81) (h : Conditions q) : valuation q 1625 = false ∨ valuation q 1652 = false ∨ valuation q 1663 = true := by
  have hs : count1655 q = (countLit q [-61, -62, -64, -67, -68, -69, -72, -73]) + (countLit q [-76, -77, -79, -80, -84, -85, -88, -90]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-61, -62, -64, -67, -68, -69, -72, -73]) (l₂ := [-76, -77, -79, -80, -84, -85, -88, -90])
  have hm := merge_two (literal (valuation q) (1625)) (literal (valuation q) (1652)) (literal (valuation q) (1663)) (countLit q [-61, -62, -64, -67, -68, -69, -72, -73]) (countLit q [-76, -77, -79, -80, -84, -85, -88, -90]) (count1655 q) 3 6 (meaning1625 q) (meaning1652 q) (meaning1663 q) hs
  change valuation q 1625 = false ∨ valuation q 1652 = false ∨ valuation q 1663 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1299 (q : Snake 81) (h : Conditions q) : valuation q 1625 = false ∨ valuation q 1653 = false ∨ valuation q 1664 = true := by
  have hs : count1655 q = (countLit q [-61, -62, -64, -67, -68, -69, -72, -73]) + (countLit q [-76, -77, -79, -80, -84, -85, -88, -90]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-61, -62, -64, -67, -68, -69, -72, -73]) (l₂ := [-76, -77, -79, -80, -84, -85, -88, -90])
  have hm := merge_two (literal (valuation q) (1625)) (literal (valuation q) (1653)) (literal (valuation q) (1664)) (countLit q [-61, -62, -64, -67, -68, -69, -72, -73]) (countLit q [-76, -77, -79, -80, -84, -85, -88, -90]) (count1655 q) 3 7 (meaning1625 q) (meaning1653 q) (meaning1664 q) hs
  change valuation q 1625 = false ∨ valuation q 1653 = false ∨ valuation q 1664 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1300 (q : Snake 81) (h : Conditions q) : valuation q 1626 = false ∨ valuation q 1647 = false ∨ valuation q 1659 = true := by
  have hs : count1655 q = (countLit q [-61, -62, -64, -67, -68, -69, -72, -73]) + (countLit q [-76, -77, -79, -80, -84, -85, -88, -90]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-61, -62, -64, -67, -68, -69, -72, -73]) (l₂ := [-76, -77, -79, -80, -84, -85, -88, -90])
  have hm := merge_two (literal (valuation q) (1626)) (literal (valuation q) (1647)) (literal (valuation q) (1659)) (countLit q [-61, -62, -64, -67, -68, -69, -72, -73]) (countLit q [-76, -77, -79, -80, -84, -85, -88, -90]) (count1655 q) 4 1 (meaning1626 q) (meaning1647 q) (meaning1659 q) hs
  change valuation q 1626 = false ∨ valuation q 1647 = false ∨ valuation q 1659 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1301 (q : Snake 81) (h : Conditions q) : valuation q 1626 = false ∨ valuation q 1648 = false ∨ valuation q 1660 = true := by
  have hs : count1655 q = (countLit q [-61, -62, -64, -67, -68, -69, -72, -73]) + (countLit q [-76, -77, -79, -80, -84, -85, -88, -90]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-61, -62, -64, -67, -68, -69, -72, -73]) (l₂ := [-76, -77, -79, -80, -84, -85, -88, -90])
  have hm := merge_two (literal (valuation q) (1626)) (literal (valuation q) (1648)) (literal (valuation q) (1660)) (countLit q [-61, -62, -64, -67, -68, -69, -72, -73]) (countLit q [-76, -77, -79, -80, -84, -85, -88, -90]) (count1655 q) 4 2 (meaning1626 q) (meaning1648 q) (meaning1660 q) hs
  change valuation q 1626 = false ∨ valuation q 1648 = false ∨ valuation q 1660 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1302 (q : Snake 81) (h : Conditions q) : valuation q 1626 = false ∨ valuation q 1649 = false ∨ valuation q 1661 = true := by
  have hs : count1655 q = (countLit q [-61, -62, -64, -67, -68, -69, -72, -73]) + (countLit q [-76, -77, -79, -80, -84, -85, -88, -90]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-61, -62, -64, -67, -68, -69, -72, -73]) (l₂ := [-76, -77, -79, -80, -84, -85, -88, -90])
  have hm := merge_two (literal (valuation q) (1626)) (literal (valuation q) (1649)) (literal (valuation q) (1661)) (countLit q [-61, -62, -64, -67, -68, -69, -72, -73]) (countLit q [-76, -77, -79, -80, -84, -85, -88, -90]) (count1655 q) 4 3 (meaning1626 q) (meaning1649 q) (meaning1661 q) hs
  change valuation q 1626 = false ∨ valuation q 1649 = false ∨ valuation q 1661 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1303 (q : Snake 81) (h : Conditions q) : valuation q 1626 = false ∨ valuation q 1650 = false ∨ valuation q 1662 = true := by
  have hs : count1655 q = (countLit q [-61, -62, -64, -67, -68, -69, -72, -73]) + (countLit q [-76, -77, -79, -80, -84, -85, -88, -90]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-61, -62, -64, -67, -68, -69, -72, -73]) (l₂ := [-76, -77, -79, -80, -84, -85, -88, -90])
  have hm := merge_two (literal (valuation q) (1626)) (literal (valuation q) (1650)) (literal (valuation q) (1662)) (countLit q [-61, -62, -64, -67, -68, -69, -72, -73]) (countLit q [-76, -77, -79, -80, -84, -85, -88, -90]) (count1655 q) 4 4 (meaning1626 q) (meaning1650 q) (meaning1662 q) hs
  change valuation q 1626 = false ∨ valuation q 1650 = false ∨ valuation q 1662 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1304 (q : Snake 81) (h : Conditions q) : valuation q 1626 = false ∨ valuation q 1651 = false ∨ valuation q 1663 = true := by
  have hs : count1655 q = (countLit q [-61, -62, -64, -67, -68, -69, -72, -73]) + (countLit q [-76, -77, -79, -80, -84, -85, -88, -90]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-61, -62, -64, -67, -68, -69, -72, -73]) (l₂ := [-76, -77, -79, -80, -84, -85, -88, -90])
  have hm := merge_two (literal (valuation q) (1626)) (literal (valuation q) (1651)) (literal (valuation q) (1663)) (countLit q [-61, -62, -64, -67, -68, -69, -72, -73]) (countLit q [-76, -77, -79, -80, -84, -85, -88, -90]) (count1655 q) 4 5 (meaning1626 q) (meaning1651 q) (meaning1663 q) hs
  change valuation q 1626 = false ∨ valuation q 1651 = false ∨ valuation q 1663 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1305 (q : Snake 81) (h : Conditions q) : valuation q 1626 = false ∨ valuation q 1652 = false ∨ valuation q 1664 = true := by
  have hs : count1655 q = (countLit q [-61, -62, -64, -67, -68, -69, -72, -73]) + (countLit q [-76, -77, -79, -80, -84, -85, -88, -90]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-61, -62, -64, -67, -68, -69, -72, -73]) (l₂ := [-76, -77, -79, -80, -84, -85, -88, -90])
  have hm := merge_two (literal (valuation q) (1626)) (literal (valuation q) (1652)) (literal (valuation q) (1664)) (countLit q [-61, -62, -64, -67, -68, -69, -72, -73]) (countLit q [-76, -77, -79, -80, -84, -85, -88, -90]) (count1655 q) 4 6 (meaning1626 q) (meaning1652 q) (meaning1664 q) hs
  change valuation q 1626 = false ∨ valuation q 1652 = false ∨ valuation q 1664 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1306 (q : Snake 81) (h : Conditions q) : valuation q 1627 = false ∨ valuation q 1647 = false ∨ valuation q 1660 = true := by
  have hs : count1655 q = (countLit q [-61, -62, -64, -67, -68, -69, -72, -73]) + (countLit q [-76, -77, -79, -80, -84, -85, -88, -90]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-61, -62, -64, -67, -68, -69, -72, -73]) (l₂ := [-76, -77, -79, -80, -84, -85, -88, -90])
  have hm := merge_two (literal (valuation q) (1627)) (literal (valuation q) (1647)) (literal (valuation q) (1660)) (countLit q [-61, -62, -64, -67, -68, -69, -72, -73]) (countLit q [-76, -77, -79, -80, -84, -85, -88, -90]) (count1655 q) 5 1 (meaning1627 q) (meaning1647 q) (meaning1660 q) hs
  change valuation q 1627 = false ∨ valuation q 1647 = false ∨ valuation q 1660 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1307 (q : Snake 81) (h : Conditions q) : valuation q 1627 = false ∨ valuation q 1648 = false ∨ valuation q 1661 = true := by
  have hs : count1655 q = (countLit q [-61, -62, -64, -67, -68, -69, -72, -73]) + (countLit q [-76, -77, -79, -80, -84, -85, -88, -90]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-61, -62, -64, -67, -68, -69, -72, -73]) (l₂ := [-76, -77, -79, -80, -84, -85, -88, -90])
  have hm := merge_two (literal (valuation q) (1627)) (literal (valuation q) (1648)) (literal (valuation q) (1661)) (countLit q [-61, -62, -64, -67, -68, -69, -72, -73]) (countLit q [-76, -77, -79, -80, -84, -85, -88, -90]) (count1655 q) 5 2 (meaning1627 q) (meaning1648 q) (meaning1661 q) hs
  change valuation q 1627 = false ∨ valuation q 1648 = false ∨ valuation q 1661 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1308 (q : Snake 81) (h : Conditions q) : valuation q 1627 = false ∨ valuation q 1649 = false ∨ valuation q 1662 = true := by
  have hs : count1655 q = (countLit q [-61, -62, -64, -67, -68, -69, -72, -73]) + (countLit q [-76, -77, -79, -80, -84, -85, -88, -90]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-61, -62, -64, -67, -68, -69, -72, -73]) (l₂ := [-76, -77, -79, -80, -84, -85, -88, -90])
  have hm := merge_two (literal (valuation q) (1627)) (literal (valuation q) (1649)) (literal (valuation q) (1662)) (countLit q [-61, -62, -64, -67, -68, -69, -72, -73]) (countLit q [-76, -77, -79, -80, -84, -85, -88, -90]) (count1655 q) 5 3 (meaning1627 q) (meaning1649 q) (meaning1662 q) hs
  change valuation q 1627 = false ∨ valuation q 1649 = false ∨ valuation q 1662 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1309 (q : Snake 81) (h : Conditions q) : valuation q 1627 = false ∨ valuation q 1650 = false ∨ valuation q 1663 = true := by
  have hs : count1655 q = (countLit q [-61, -62, -64, -67, -68, -69, -72, -73]) + (countLit q [-76, -77, -79, -80, -84, -85, -88, -90]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-61, -62, -64, -67, -68, -69, -72, -73]) (l₂ := [-76, -77, -79, -80, -84, -85, -88, -90])
  have hm := merge_two (literal (valuation q) (1627)) (literal (valuation q) (1650)) (literal (valuation q) (1663)) (countLit q [-61, -62, -64, -67, -68, -69, -72, -73]) (countLit q [-76, -77, -79, -80, -84, -85, -88, -90]) (count1655 q) 5 4 (meaning1627 q) (meaning1650 q) (meaning1663 q) hs
  change valuation q 1627 = false ∨ valuation q 1650 = false ∨ valuation q 1663 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1310 (q : Snake 81) (h : Conditions q) : valuation q 1627 = false ∨ valuation q 1651 = false ∨ valuation q 1664 = true := by
  have hs : count1655 q = (countLit q [-61, -62, -64, -67, -68, -69, -72, -73]) + (countLit q [-76, -77, -79, -80, -84, -85, -88, -90]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-61, -62, -64, -67, -68, -69, -72, -73]) (l₂ := [-76, -77, -79, -80, -84, -85, -88, -90])
  have hm := merge_two (literal (valuation q) (1627)) (literal (valuation q) (1651)) (literal (valuation q) (1664)) (countLit q [-61, -62, -64, -67, -68, -69, -72, -73]) (countLit q [-76, -77, -79, -80, -84, -85, -88, -90]) (count1655 q) 5 5 (meaning1627 q) (meaning1651 q) (meaning1664 q) hs
  change valuation q 1627 = false ∨ valuation q 1651 = false ∨ valuation q 1664 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1311 (q : Snake 81) (h : Conditions q) : valuation q 1628 = false ∨ valuation q 1648 = false ∨ valuation q 1662 = true := by
  have hs : count1655 q = (countLit q [-61, -62, -64, -67, -68, -69, -72, -73]) + (countLit q [-76, -77, -79, -80, -84, -85, -88, -90]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-61, -62, -64, -67, -68, -69, -72, -73]) (l₂ := [-76, -77, -79, -80, -84, -85, -88, -90])
  have hm := merge_two (literal (valuation q) (1628)) (literal (valuation q) (1648)) (literal (valuation q) (1662)) (countLit q [-61, -62, -64, -67, -68, -69, -72, -73]) (countLit q [-76, -77, -79, -80, -84, -85, -88, -90]) (count1655 q) 6 2 (meaning1628 q) (meaning1648 q) (meaning1662 q) hs
  change valuation q 1628 = false ∨ valuation q 1648 = false ∨ valuation q 1662 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1312 (q : Snake 81) (h : Conditions q) : valuation q 1628 = false ∨ valuation q 1649 = false ∨ valuation q 1663 = true := by
  have hs : count1655 q = (countLit q [-61, -62, -64, -67, -68, -69, -72, -73]) + (countLit q [-76, -77, -79, -80, -84, -85, -88, -90]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-61, -62, -64, -67, -68, -69, -72, -73]) (l₂ := [-76, -77, -79, -80, -84, -85, -88, -90])
  have hm := merge_two (literal (valuation q) (1628)) (literal (valuation q) (1649)) (literal (valuation q) (1663)) (countLit q [-61, -62, -64, -67, -68, -69, -72, -73]) (countLit q [-76, -77, -79, -80, -84, -85, -88, -90]) (count1655 q) 6 3 (meaning1628 q) (meaning1649 q) (meaning1663 q) hs
  change valuation q 1628 = false ∨ valuation q 1649 = false ∨ valuation q 1663 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem block40 (q : Snake 81) (h : Conditions q) : Dfs112FirstBoolean.Block40 (valuation q) :=
  ⟨clause1281 q h, clause1282 q h, clause1283 q h, clause1284 q h, clause1285 q h, clause1286 q h, clause1287 q h, clause1288 q h, clause1289 q h, clause1290 q h, clause1291 q h, clause1292 q h, clause1293 q h, clause1294 q h, clause1295 q h, clause1296 q h, clause1297 q h, clause1298 q h, clause1299 q h, clause1300 q h, clause1301 q h, clause1302 q h, clause1303 q h, clause1304 q h, clause1305 q h, clause1306 q h, clause1307 q h, clause1308 q h, clause1309 q h, clause1310 q h, clause1311 q h, clause1312 q h⟩

end
end Snake9.Regrowth.First112
