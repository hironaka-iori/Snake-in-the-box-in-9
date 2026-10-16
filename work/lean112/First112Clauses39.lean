import First112Semantics
import Dfs112FirstBooleanInputs
namespace Snake9.Regrowth.First112
noncomputable section
local instance blockDec39 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause1249 (q : Snake 81) (h : Conditions q) : valuation q 1641 = false ∨ valuation q 1643 = true := by
  have hs : count1643 q = (countLit q [-84, -85]) + (countLit q [-88, -90]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-84, -85]) (l₂ := [-88, -90])
  have hm := merge_right (literal (valuation q) (1641)) (literal (valuation q) (1643)) (countLit q [-84, -85]) (countLit q [-88, -90]) (count1643 q) 1 (meaning1641 q) (meaning1643 q) hs
  change valuation q 1641 = false ∨ valuation q 1643 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1250 (q : Snake 81) (h : Conditions q) : valuation q 1642 = false ∨ valuation q 1644 = true := by
  have hs : count1643 q = (countLit q [-84, -85]) + (countLit q [-88, -90]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-84, -85]) (l₂ := [-88, -90])
  have hm := merge_right (literal (valuation q) (1642)) (literal (valuation q) (1644)) (countLit q [-84, -85]) (countLit q [-88, -90]) (count1643 q) 2 (meaning1642 q) (meaning1644 q) hs
  change valuation q 1642 = false ∨ valuation q 1644 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1251 (q : Snake 81) (h : Conditions q) : valuation q 1639 = false ∨ valuation q 1643 = true := by
  have hs : count1643 q = (countLit q [-84, -85]) + (countLit q [-88, -90]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-84, -85]) (l₂ := [-88, -90])
  have hm := merge_left (literal (valuation q) (1639)) (literal (valuation q) (1643)) (countLit q [-84, -85]) (countLit q [-88, -90]) (count1643 q) 1 (meaning1639 q) (meaning1643 q) hs
  change valuation q 1639 = false ∨ valuation q 1643 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1252 (q : Snake 81) (h : Conditions q) : valuation q 1639 = false ∨ valuation q 1641 = false ∨ valuation q 1644 = true := by
  have hs : count1643 q = (countLit q [-84, -85]) + (countLit q [-88, -90]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-84, -85]) (l₂ := [-88, -90])
  have hm := merge_two (literal (valuation q) (1639)) (literal (valuation q) (1641)) (literal (valuation q) (1644)) (countLit q [-84, -85]) (countLit q [-88, -90]) (count1643 q) 1 1 (meaning1639 q) (meaning1641 q) (meaning1644 q) hs
  change valuation q 1639 = false ∨ valuation q 1641 = false ∨ valuation q 1644 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1253 (q : Snake 81) (h : Conditions q) : valuation q 1639 = false ∨ valuation q 1642 = false ∨ valuation q 1645 = true := by
  have hs : count1643 q = (countLit q [-84, -85]) + (countLit q [-88, -90]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-84, -85]) (l₂ := [-88, -90])
  have hm := merge_two (literal (valuation q) (1639)) (literal (valuation q) (1642)) (literal (valuation q) (1645)) (countLit q [-84, -85]) (countLit q [-88, -90]) (count1643 q) 1 2 (meaning1639 q) (meaning1642 q) (meaning1645 q) hs
  change valuation q 1639 = false ∨ valuation q 1642 = false ∨ valuation q 1645 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1254 (q : Snake 81) (h : Conditions q) : valuation q 1640 = false ∨ valuation q 1644 = true := by
  have hs : count1643 q = (countLit q [-84, -85]) + (countLit q [-88, -90]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-84, -85]) (l₂ := [-88, -90])
  have hm := merge_left (literal (valuation q) (1640)) (literal (valuation q) (1644)) (countLit q [-84, -85]) (countLit q [-88, -90]) (count1643 q) 2 (meaning1640 q) (meaning1644 q) hs
  change valuation q 1640 = false ∨ valuation q 1644 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1255 (q : Snake 81) (h : Conditions q) : valuation q 1640 = false ∨ valuation q 1641 = false ∨ valuation q 1645 = true := by
  have hs : count1643 q = (countLit q [-84, -85]) + (countLit q [-88, -90]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-84, -85]) (l₂ := [-88, -90])
  have hm := merge_two (literal (valuation q) (1640)) (literal (valuation q) (1641)) (literal (valuation q) (1645)) (countLit q [-84, -85]) (countLit q [-88, -90]) (count1643 q) 2 1 (meaning1640 q) (meaning1641 q) (meaning1645 q) hs
  change valuation q 1640 = false ∨ valuation q 1641 = false ∨ valuation q 1645 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1256 (q : Snake 81) (h : Conditions q) : valuation q 1640 = false ∨ valuation q 1642 = false ∨ valuation q 1646 = true := by
  have hs : count1643 q = (countLit q [-84, -85]) + (countLit q [-88, -90]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-84, -85]) (l₂ := [-88, -90])
  have hm := merge_two (literal (valuation q) (1640)) (literal (valuation q) (1642)) (literal (valuation q) (1646)) (countLit q [-84, -85]) (countLit q [-88, -90]) (count1643 q) 2 2 (meaning1640 q) (meaning1642 q) (meaning1646 q) hs
  change valuation q 1640 = false ∨ valuation q 1642 = false ∨ valuation q 1646 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1257 (q : Snake 81) (h : Conditions q) : valuation q 1643 = false ∨ valuation q 1647 = true := by
  have hs : count1647 q = (countLit q [-76, -77, -79, -80]) + (countLit q [-84, -85, -88, -90]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-76, -77, -79, -80]) (l₂ := [-84, -85, -88, -90])
  have hm := merge_right (literal (valuation q) (1643)) (literal (valuation q) (1647)) (countLit q [-76, -77, -79, -80]) (countLit q [-84, -85, -88, -90]) (count1647 q) 1 (meaning1643 q) (meaning1647 q) hs
  change valuation q 1643 = false ∨ valuation q 1647 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1258 (q : Snake 81) (h : Conditions q) : valuation q 1644 = false ∨ valuation q 1648 = true := by
  have hs : count1647 q = (countLit q [-76, -77, -79, -80]) + (countLit q [-84, -85, -88, -90]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-76, -77, -79, -80]) (l₂ := [-84, -85, -88, -90])
  have hm := merge_right (literal (valuation q) (1644)) (literal (valuation q) (1648)) (countLit q [-76, -77, -79, -80]) (countLit q [-84, -85, -88, -90]) (count1647 q) 2 (meaning1644 q) (meaning1648 q) hs
  change valuation q 1644 = false ∨ valuation q 1648 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1259 (q : Snake 81) (h : Conditions q) : valuation q 1645 = false ∨ valuation q 1649 = true := by
  have hs : count1647 q = (countLit q [-76, -77, -79, -80]) + (countLit q [-84, -85, -88, -90]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-76, -77, -79, -80]) (l₂ := [-84, -85, -88, -90])
  have hm := merge_right (literal (valuation q) (1645)) (literal (valuation q) (1649)) (countLit q [-76, -77, -79, -80]) (countLit q [-84, -85, -88, -90]) (count1647 q) 3 (meaning1645 q) (meaning1649 q) hs
  change valuation q 1645 = false ∨ valuation q 1649 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1260 (q : Snake 81) (h : Conditions q) : valuation q 1646 = false ∨ valuation q 1650 = true := by
  have hs : count1647 q = (countLit q [-76, -77, -79, -80]) + (countLit q [-84, -85, -88, -90]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-76, -77, -79, -80]) (l₂ := [-84, -85, -88, -90])
  have hm := merge_right (literal (valuation q) (1646)) (literal (valuation q) (1650)) (countLit q [-76, -77, -79, -80]) (countLit q [-84, -85, -88, -90]) (count1647 q) 4 (meaning1646 q) (meaning1650 q) hs
  change valuation q 1646 = false ∨ valuation q 1650 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1261 (q : Snake 81) (h : Conditions q) : valuation q 1635 = false ∨ valuation q 1643 = false ∨ valuation q 1648 = true := by
  have hs : count1647 q = (countLit q [-76, -77, -79, -80]) + (countLit q [-84, -85, -88, -90]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-76, -77, -79, -80]) (l₂ := [-84, -85, -88, -90])
  have hm := merge_two (literal (valuation q) (1635)) (literal (valuation q) (1643)) (literal (valuation q) (1648)) (countLit q [-76, -77, -79, -80]) (countLit q [-84, -85, -88, -90]) (count1647 q) 1 1 (meaning1635 q) (meaning1643 q) (meaning1648 q) hs
  change valuation q 1635 = false ∨ valuation q 1643 = false ∨ valuation q 1648 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1262 (q : Snake 81) (h : Conditions q) : valuation q 1635 = false ∨ valuation q 1644 = false ∨ valuation q 1649 = true := by
  have hs : count1647 q = (countLit q [-76, -77, -79, -80]) + (countLit q [-84, -85, -88, -90]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-76, -77, -79, -80]) (l₂ := [-84, -85, -88, -90])
  have hm := merge_two (literal (valuation q) (1635)) (literal (valuation q) (1644)) (literal (valuation q) (1649)) (countLit q [-76, -77, -79, -80]) (countLit q [-84, -85, -88, -90]) (count1647 q) 1 2 (meaning1635 q) (meaning1644 q) (meaning1649 q) hs
  change valuation q 1635 = false ∨ valuation q 1644 = false ∨ valuation q 1649 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1263 (q : Snake 81) (h : Conditions q) : valuation q 1635 = false ∨ valuation q 1645 = false ∨ valuation q 1650 = true := by
  have hs : count1647 q = (countLit q [-76, -77, -79, -80]) + (countLit q [-84, -85, -88, -90]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-76, -77, -79, -80]) (l₂ := [-84, -85, -88, -90])
  have hm := merge_two (literal (valuation q) (1635)) (literal (valuation q) (1645)) (literal (valuation q) (1650)) (countLit q [-76, -77, -79, -80]) (countLit q [-84, -85, -88, -90]) (count1647 q) 1 3 (meaning1635 q) (meaning1645 q) (meaning1650 q) hs
  change valuation q 1635 = false ∨ valuation q 1645 = false ∨ valuation q 1650 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1264 (q : Snake 81) (h : Conditions q) : valuation q 1635 = false ∨ valuation q 1646 = false ∨ valuation q 1651 = true := by
  have hs : count1647 q = (countLit q [-76, -77, -79, -80]) + (countLit q [-84, -85, -88, -90]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-76, -77, -79, -80]) (l₂ := [-84, -85, -88, -90])
  have hm := merge_two (literal (valuation q) (1635)) (literal (valuation q) (1646)) (literal (valuation q) (1651)) (countLit q [-76, -77, -79, -80]) (countLit q [-84, -85, -88, -90]) (count1647 q) 1 4 (meaning1635 q) (meaning1646 q) (meaning1651 q) hs
  change valuation q 1635 = false ∨ valuation q 1646 = false ∨ valuation q 1651 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1265 (q : Snake 81) (h : Conditions q) : valuation q 1636 = false ∨ valuation q 1648 = true := by
  have hs : count1647 q = (countLit q [-76, -77, -79, -80]) + (countLit q [-84, -85, -88, -90]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-76, -77, -79, -80]) (l₂ := [-84, -85, -88, -90])
  have hm := merge_left (literal (valuation q) (1636)) (literal (valuation q) (1648)) (countLit q [-76, -77, -79, -80]) (countLit q [-84, -85, -88, -90]) (count1647 q) 2 (meaning1636 q) (meaning1648 q) hs
  change valuation q 1636 = false ∨ valuation q 1648 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1266 (q : Snake 81) (h : Conditions q) : valuation q 1636 = false ∨ valuation q 1643 = false ∨ valuation q 1649 = true := by
  have hs : count1647 q = (countLit q [-76, -77, -79, -80]) + (countLit q [-84, -85, -88, -90]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-76, -77, -79, -80]) (l₂ := [-84, -85, -88, -90])
  have hm := merge_two (literal (valuation q) (1636)) (literal (valuation q) (1643)) (literal (valuation q) (1649)) (countLit q [-76, -77, -79, -80]) (countLit q [-84, -85, -88, -90]) (count1647 q) 2 1 (meaning1636 q) (meaning1643 q) (meaning1649 q) hs
  change valuation q 1636 = false ∨ valuation q 1643 = false ∨ valuation q 1649 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1267 (q : Snake 81) (h : Conditions q) : valuation q 1636 = false ∨ valuation q 1644 = false ∨ valuation q 1650 = true := by
  have hs : count1647 q = (countLit q [-76, -77, -79, -80]) + (countLit q [-84, -85, -88, -90]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-76, -77, -79, -80]) (l₂ := [-84, -85, -88, -90])
  have hm := merge_two (literal (valuation q) (1636)) (literal (valuation q) (1644)) (literal (valuation q) (1650)) (countLit q [-76, -77, -79, -80]) (countLit q [-84, -85, -88, -90]) (count1647 q) 2 2 (meaning1636 q) (meaning1644 q) (meaning1650 q) hs
  change valuation q 1636 = false ∨ valuation q 1644 = false ∨ valuation q 1650 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1268 (q : Snake 81) (h : Conditions q) : valuation q 1636 = false ∨ valuation q 1645 = false ∨ valuation q 1651 = true := by
  have hs : count1647 q = (countLit q [-76, -77, -79, -80]) + (countLit q [-84, -85, -88, -90]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-76, -77, -79, -80]) (l₂ := [-84, -85, -88, -90])
  have hm := merge_two (literal (valuation q) (1636)) (literal (valuation q) (1645)) (literal (valuation q) (1651)) (countLit q [-76, -77, -79, -80]) (countLit q [-84, -85, -88, -90]) (count1647 q) 2 3 (meaning1636 q) (meaning1645 q) (meaning1651 q) hs
  change valuation q 1636 = false ∨ valuation q 1645 = false ∨ valuation q 1651 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1269 (q : Snake 81) (h : Conditions q) : valuation q 1636 = false ∨ valuation q 1646 = false ∨ valuation q 1652 = true := by
  have hs : count1647 q = (countLit q [-76, -77, -79, -80]) + (countLit q [-84, -85, -88, -90]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-76, -77, -79, -80]) (l₂ := [-84, -85, -88, -90])
  have hm := merge_two (literal (valuation q) (1636)) (literal (valuation q) (1646)) (literal (valuation q) (1652)) (countLit q [-76, -77, -79, -80]) (countLit q [-84, -85, -88, -90]) (count1647 q) 2 4 (meaning1636 q) (meaning1646 q) (meaning1652 q) hs
  change valuation q 1636 = false ∨ valuation q 1646 = false ∨ valuation q 1652 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1270 (q : Snake 81) (h : Conditions q) : valuation q 1637 = false ∨ valuation q 1649 = true := by
  have hs : count1647 q = (countLit q [-76, -77, -79, -80]) + (countLit q [-84, -85, -88, -90]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-76, -77, -79, -80]) (l₂ := [-84, -85, -88, -90])
  have hm := merge_left (literal (valuation q) (1637)) (literal (valuation q) (1649)) (countLit q [-76, -77, -79, -80]) (countLit q [-84, -85, -88, -90]) (count1647 q) 3 (meaning1637 q) (meaning1649 q) hs
  change valuation q 1637 = false ∨ valuation q 1649 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1271 (q : Snake 81) (h : Conditions q) : valuation q 1637 = false ∨ valuation q 1643 = false ∨ valuation q 1650 = true := by
  have hs : count1647 q = (countLit q [-76, -77, -79, -80]) + (countLit q [-84, -85, -88, -90]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-76, -77, -79, -80]) (l₂ := [-84, -85, -88, -90])
  have hm := merge_two (literal (valuation q) (1637)) (literal (valuation q) (1643)) (literal (valuation q) (1650)) (countLit q [-76, -77, -79, -80]) (countLit q [-84, -85, -88, -90]) (count1647 q) 3 1 (meaning1637 q) (meaning1643 q) (meaning1650 q) hs
  change valuation q 1637 = false ∨ valuation q 1643 = false ∨ valuation q 1650 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1272 (q : Snake 81) (h : Conditions q) : valuation q 1637 = false ∨ valuation q 1644 = false ∨ valuation q 1651 = true := by
  have hs : count1647 q = (countLit q [-76, -77, -79, -80]) + (countLit q [-84, -85, -88, -90]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-76, -77, -79, -80]) (l₂ := [-84, -85, -88, -90])
  have hm := merge_two (literal (valuation q) (1637)) (literal (valuation q) (1644)) (literal (valuation q) (1651)) (countLit q [-76, -77, -79, -80]) (countLit q [-84, -85, -88, -90]) (count1647 q) 3 2 (meaning1637 q) (meaning1644 q) (meaning1651 q) hs
  change valuation q 1637 = false ∨ valuation q 1644 = false ∨ valuation q 1651 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1273 (q : Snake 81) (h : Conditions q) : valuation q 1637 = false ∨ valuation q 1645 = false ∨ valuation q 1652 = true := by
  have hs : count1647 q = (countLit q [-76, -77, -79, -80]) + (countLit q [-84, -85, -88, -90]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-76, -77, -79, -80]) (l₂ := [-84, -85, -88, -90])
  have hm := merge_two (literal (valuation q) (1637)) (literal (valuation q) (1645)) (literal (valuation q) (1652)) (countLit q [-76, -77, -79, -80]) (countLit q [-84, -85, -88, -90]) (count1647 q) 3 3 (meaning1637 q) (meaning1645 q) (meaning1652 q) hs
  change valuation q 1637 = false ∨ valuation q 1645 = false ∨ valuation q 1652 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1274 (q : Snake 81) (h : Conditions q) : valuation q 1637 = false ∨ valuation q 1646 = false ∨ valuation q 1653 = true := by
  have hs : count1647 q = (countLit q [-76, -77, -79, -80]) + (countLit q [-84, -85, -88, -90]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-76, -77, -79, -80]) (l₂ := [-84, -85, -88, -90])
  have hm := merge_two (literal (valuation q) (1637)) (literal (valuation q) (1646)) (literal (valuation q) (1653)) (countLit q [-76, -77, -79, -80]) (countLit q [-84, -85, -88, -90]) (count1647 q) 3 4 (meaning1637 q) (meaning1646 q) (meaning1653 q) hs
  change valuation q 1637 = false ∨ valuation q 1646 = false ∨ valuation q 1653 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1275 (q : Snake 81) (h : Conditions q) : valuation q 1648 = false ∨ valuation q 1656 = true := by
  have hs : count1655 q = (countLit q [-61, -62, -64, -67, -68, -69, -72, -73]) + (countLit q [-76, -77, -79, -80, -84, -85, -88, -90]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-61, -62, -64, -67, -68, -69, -72, -73]) (l₂ := [-76, -77, -79, -80, -84, -85, -88, -90])
  have hm := merge_right (literal (valuation q) (1648)) (literal (valuation q) (1656)) (countLit q [-61, -62, -64, -67, -68, -69, -72, -73]) (countLit q [-76, -77, -79, -80, -84, -85, -88, -90]) (count1655 q) 2 (meaning1648 q) (meaning1656 q) hs
  change valuation q 1648 = false ∨ valuation q 1656 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1276 (q : Snake 81) (h : Conditions q) : valuation q 1649 = false ∨ valuation q 1657 = true := by
  have hs : count1655 q = (countLit q [-61, -62, -64, -67, -68, -69, -72, -73]) + (countLit q [-76, -77, -79, -80, -84, -85, -88, -90]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-61, -62, -64, -67, -68, -69, -72, -73]) (l₂ := [-76, -77, -79, -80, -84, -85, -88, -90])
  have hm := merge_right (literal (valuation q) (1649)) (literal (valuation q) (1657)) (countLit q [-61, -62, -64, -67, -68, -69, -72, -73]) (countLit q [-76, -77, -79, -80, -84, -85, -88, -90]) (count1655 q) 3 (meaning1649 q) (meaning1657 q) hs
  change valuation q 1649 = false ∨ valuation q 1657 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1277 (q : Snake 81) (h : Conditions q) : valuation q 1650 = false ∨ valuation q 1658 = true := by
  have hs : count1655 q = (countLit q [-61, -62, -64, -67, -68, -69, -72, -73]) + (countLit q [-76, -77, -79, -80, -84, -85, -88, -90]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-61, -62, -64, -67, -68, -69, -72, -73]) (l₂ := [-76, -77, -79, -80, -84, -85, -88, -90])
  have hm := merge_right (literal (valuation q) (1650)) (literal (valuation q) (1658)) (countLit q [-61, -62, -64, -67, -68, -69, -72, -73]) (countLit q [-76, -77, -79, -80, -84, -85, -88, -90]) (count1655 q) 4 (meaning1650 q) (meaning1658 q) hs
  change valuation q 1650 = false ∨ valuation q 1658 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1278 (q : Snake 81) (h : Conditions q) : valuation q 1651 = false ∨ valuation q 1659 = true := by
  have hs : count1655 q = (countLit q [-61, -62, -64, -67, -68, -69, -72, -73]) + (countLit q [-76, -77, -79, -80, -84, -85, -88, -90]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-61, -62, -64, -67, -68, -69, -72, -73]) (l₂ := [-76, -77, -79, -80, -84, -85, -88, -90])
  have hm := merge_right (literal (valuation q) (1651)) (literal (valuation q) (1659)) (countLit q [-61, -62, -64, -67, -68, -69, -72, -73]) (countLit q [-76, -77, -79, -80, -84, -85, -88, -90]) (count1655 q) 5 (meaning1651 q) (meaning1659 q) hs
  change valuation q 1651 = false ∨ valuation q 1659 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1279 (q : Snake 81) (h : Conditions q) : valuation q 1652 = false ∨ valuation q 1660 = true := by
  have hs : count1655 q = (countLit q [-61, -62, -64, -67, -68, -69, -72, -73]) + (countLit q [-76, -77, -79, -80, -84, -85, -88, -90]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-61, -62, -64, -67, -68, -69, -72, -73]) (l₂ := [-76, -77, -79, -80, -84, -85, -88, -90])
  have hm := merge_right (literal (valuation q) (1652)) (literal (valuation q) (1660)) (countLit q [-61, -62, -64, -67, -68, -69, -72, -73]) (countLit q [-76, -77, -79, -80, -84, -85, -88, -90]) (count1655 q) 6 (meaning1652 q) (meaning1660 q) hs
  change valuation q 1652 = false ∨ valuation q 1660 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1280 (q : Snake 81) (h : Conditions q) : valuation q 1623 = false ∨ valuation q 1647 = false ∨ valuation q 1656 = true := by
  have hs : count1655 q = (countLit q [-61, -62, -64, -67, -68, -69, -72, -73]) + (countLit q [-76, -77, -79, -80, -84, -85, -88, -90]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-61, -62, -64, -67, -68, -69, -72, -73]) (l₂ := [-76, -77, -79, -80, -84, -85, -88, -90])
  have hm := merge_two (literal (valuation q) (1623)) (literal (valuation q) (1647)) (literal (valuation q) (1656)) (countLit q [-61, -62, -64, -67, -68, -69, -72, -73]) (countLit q [-76, -77, -79, -80, -84, -85, -88, -90]) (count1655 q) 1 1 (meaning1623 q) (meaning1647 q) (meaning1656 q) hs
  change valuation q 1623 = false ∨ valuation q 1647 = false ∨ valuation q 1656 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem block39 (q : Snake 81) (h : Conditions q) : Dfs112FirstBoolean.Block39 (valuation q) :=
  ⟨clause1249 q h, clause1250 q h, clause1251 q h, clause1252 q h, clause1253 q h, clause1254 q h, clause1255 q h, clause1256 q h, clause1257 q h, clause1258 q h, clause1259 q h, clause1260 q h, clause1261 q h, clause1262 q h, clause1263 q h, clause1264 q h, clause1265 q h, clause1266 q h, clause1267 q h, clause1268 q h, clause1269 q h, clause1270 q h, clause1271 q h, clause1272 q h, clause1273 q h, clause1274 q h, clause1275 q h, clause1276 q h, clause1277 q h, clause1278 q h, clause1279 q h, clause1280 q h⟩

end
end Snake9.Regrowth.First112
