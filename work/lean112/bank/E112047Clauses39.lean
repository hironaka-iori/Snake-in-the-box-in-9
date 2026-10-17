import E112047Semantics
import B112E047Inputs
namespace Snake9.Regrowth.E112047
noncomputable section
local instance blockDec39 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1249 (q : Nat → Bool) : valuationOf q 1575 = false ∨ valuationOf q 1577 = false ∨ valuationOf q 1581 = true := by
  have hs : count1578 q = (countLit q [-67, -71]) + (countLit q [-73, -75]) := List.countP_append (p := literal q) (l₁ := [-67, -71]) (l₂ := [-73, -75])
  have hm := merge_two (literal (valuationOf q) (1575)) (literal (valuationOf q) (1577)) (literal (valuationOf q) (1581)) (countLit q [-67, -71]) (countLit q [-73, -75]) (count1578 q) 2 2 (meaning1575 q) (meaning1577 q) (meaning1581 q) hs
  change valuationOf q 1575 = false ∨ valuationOf q 1577 = false ∨ valuationOf q 1581 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1249 (q : Snake 81) (h : Conditions q) : valuation q 1575 = false ∨ valuation q 1577 = false ∨ valuation q 1581 = true := counterClause1249 (baseVal q)

theorem counterClause1250 (q : Nat → Bool) : valuationOf q 1578 = false ∨ valuationOf q 1582 = true := by
  have hs : count1582 q = (countLit q [-63, -64, -66]) + (countLit q [-67, -71, -73, -75]) := List.countP_append (p := literal q) (l₁ := [-63, -64, -66]) (l₂ := [-67, -71, -73, -75])
  have hm := merge_right (literal (valuationOf q) (1578)) (literal (valuationOf q) (1582)) (countLit q [-63, -64, -66]) (countLit q [-67, -71, -73, -75]) (count1582 q) 1 (meaning1578 q) (meaning1582 q) hs
  change valuationOf q 1578 = false ∨ valuationOf q 1582 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1250 (q : Snake 81) (h : Conditions q) : valuation q 1578 = false ∨ valuation q 1582 = true := counterClause1250 (baseVal q)

theorem counterClause1251 (q : Nat → Bool) : valuationOf q 1579 = false ∨ valuationOf q 1583 = true := by
  have hs : count1582 q = (countLit q [-63, -64, -66]) + (countLit q [-67, -71, -73, -75]) := List.countP_append (p := literal q) (l₁ := [-63, -64, -66]) (l₂ := [-67, -71, -73, -75])
  have hm := merge_right (literal (valuationOf q) (1579)) (literal (valuationOf q) (1583)) (countLit q [-63, -64, -66]) (countLit q [-67, -71, -73, -75]) (count1582 q) 2 (meaning1579 q) (meaning1583 q) hs
  change valuationOf q 1579 = false ∨ valuationOf q 1583 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1251 (q : Snake 81) (h : Conditions q) : valuation q 1579 = false ∨ valuation q 1583 = true := counterClause1251 (baseVal q)

theorem counterClause1252 (q : Nat → Bool) : valuationOf q 1580 = false ∨ valuationOf q 1584 = true := by
  have hs : count1582 q = (countLit q [-63, -64, -66]) + (countLit q [-67, -71, -73, -75]) := List.countP_append (p := literal q) (l₁ := [-63, -64, -66]) (l₂ := [-67, -71, -73, -75])
  have hm := merge_right (literal (valuationOf q) (1580)) (literal (valuationOf q) (1584)) (countLit q [-63, -64, -66]) (countLit q [-67, -71, -73, -75]) (count1582 q) 3 (meaning1580 q) (meaning1584 q) hs
  change valuationOf q 1580 = false ∨ valuationOf q 1584 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1252 (q : Snake 81) (h : Conditions q) : valuation q 1580 = false ∨ valuation q 1584 = true := counterClause1252 (baseVal q)

theorem counterClause1253 (q : Nat → Bool) : valuationOf q 1581 = false ∨ valuationOf q 1585 = true := by
  have hs : count1582 q = (countLit q [-63, -64, -66]) + (countLit q [-67, -71, -73, -75]) := List.countP_append (p := literal q) (l₁ := [-63, -64, -66]) (l₂ := [-67, -71, -73, -75])
  have hm := merge_right (literal (valuationOf q) (1581)) (literal (valuationOf q) (1585)) (countLit q [-63, -64, -66]) (countLit q [-67, -71, -73, -75]) (count1582 q) 4 (meaning1581 q) (meaning1585 q) hs
  change valuationOf q 1581 = false ∨ valuationOf q 1585 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1253 (q : Snake 81) (h : Conditions q) : valuation q 1581 = false ∨ valuation q 1585 = true := counterClause1253 (baseVal q)

theorem counterClause1254 (q : Nat → Bool) : valuationOf q 1571 = false ∨ valuationOf q 1582 = true := by
  have hs : count1582 q = (countLit q [-63, -64, -66]) + (countLit q [-67, -71, -73, -75]) := List.countP_append (p := literal q) (l₁ := [-63, -64, -66]) (l₂ := [-67, -71, -73, -75])
  have hm := merge_left (literal (valuationOf q) (1571)) (literal (valuationOf q) (1582)) (countLit q [-63, -64, -66]) (countLit q [-67, -71, -73, -75]) (count1582 q) 1 (meaning1571 q) (meaning1582 q) hs
  change valuationOf q 1571 = false ∨ valuationOf q 1582 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1254 (q : Snake 81) (h : Conditions q) : valuation q 1571 = false ∨ valuation q 1582 = true := counterClause1254 (baseVal q)

theorem counterClause1255 (q : Nat → Bool) : valuationOf q 1571 = false ∨ valuationOf q 1578 = false ∨ valuationOf q 1583 = true := by
  have hs : count1582 q = (countLit q [-63, -64, -66]) + (countLit q [-67, -71, -73, -75]) := List.countP_append (p := literal q) (l₁ := [-63, -64, -66]) (l₂ := [-67, -71, -73, -75])
  have hm := merge_two (literal (valuationOf q) (1571)) (literal (valuationOf q) (1578)) (literal (valuationOf q) (1583)) (countLit q [-63, -64, -66]) (countLit q [-67, -71, -73, -75]) (count1582 q) 1 1 (meaning1571 q) (meaning1578 q) (meaning1583 q) hs
  change valuationOf q 1571 = false ∨ valuationOf q 1578 = false ∨ valuationOf q 1583 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1255 (q : Snake 81) (h : Conditions q) : valuation q 1571 = false ∨ valuation q 1578 = false ∨ valuation q 1583 = true := counterClause1255 (baseVal q)

theorem counterClause1256 (q : Nat → Bool) : valuationOf q 1571 = false ∨ valuationOf q 1579 = false ∨ valuationOf q 1584 = true := by
  have hs : count1582 q = (countLit q [-63, -64, -66]) + (countLit q [-67, -71, -73, -75]) := List.countP_append (p := literal q) (l₁ := [-63, -64, -66]) (l₂ := [-67, -71, -73, -75])
  have hm := merge_two (literal (valuationOf q) (1571)) (literal (valuationOf q) (1579)) (literal (valuationOf q) (1584)) (countLit q [-63, -64, -66]) (countLit q [-67, -71, -73, -75]) (count1582 q) 1 2 (meaning1571 q) (meaning1579 q) (meaning1584 q) hs
  change valuationOf q 1571 = false ∨ valuationOf q 1579 = false ∨ valuationOf q 1584 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1256 (q : Snake 81) (h : Conditions q) : valuation q 1571 = false ∨ valuation q 1579 = false ∨ valuation q 1584 = true := counterClause1256 (baseVal q)

theorem counterClause1257 (q : Nat → Bool) : valuationOf q 1571 = false ∨ valuationOf q 1580 = false ∨ valuationOf q 1585 = true := by
  have hs : count1582 q = (countLit q [-63, -64, -66]) + (countLit q [-67, -71, -73, -75]) := List.countP_append (p := literal q) (l₁ := [-63, -64, -66]) (l₂ := [-67, -71, -73, -75])
  have hm := merge_two (literal (valuationOf q) (1571)) (literal (valuationOf q) (1580)) (literal (valuationOf q) (1585)) (countLit q [-63, -64, -66]) (countLit q [-67, -71, -73, -75]) (count1582 q) 1 3 (meaning1571 q) (meaning1580 q) (meaning1585 q) hs
  change valuationOf q 1571 = false ∨ valuationOf q 1580 = false ∨ valuationOf q 1585 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1257 (q : Snake 81) (h : Conditions q) : valuation q 1571 = false ∨ valuation q 1580 = false ∨ valuation q 1585 = true := counterClause1257 (baseVal q)

theorem counterClause1258 (q : Nat → Bool) : valuationOf q 1571 = false ∨ valuationOf q 1581 = false ∨ valuationOf q 1586 = true := by
  have hs : count1582 q = (countLit q [-63, -64, -66]) + (countLit q [-67, -71, -73, -75]) := List.countP_append (p := literal q) (l₁ := [-63, -64, -66]) (l₂ := [-67, -71, -73, -75])
  have hm := merge_two (literal (valuationOf q) (1571)) (literal (valuationOf q) (1581)) (literal (valuationOf q) (1586)) (countLit q [-63, -64, -66]) (countLit q [-67, -71, -73, -75]) (count1582 q) 1 4 (meaning1571 q) (meaning1581 q) (meaning1586 q) hs
  change valuationOf q 1571 = false ∨ valuationOf q 1581 = false ∨ valuationOf q 1586 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1258 (q : Snake 81) (h : Conditions q) : valuation q 1571 = false ∨ valuation q 1581 = false ∨ valuation q 1586 = true := counterClause1258 (baseVal q)

theorem counterClause1259 (q : Nat → Bool) : valuationOf q 1572 = false ∨ valuationOf q 1583 = true := by
  have hs : count1582 q = (countLit q [-63, -64, -66]) + (countLit q [-67, -71, -73, -75]) := List.countP_append (p := literal q) (l₁ := [-63, -64, -66]) (l₂ := [-67, -71, -73, -75])
  have hm := merge_left (literal (valuationOf q) (1572)) (literal (valuationOf q) (1583)) (countLit q [-63, -64, -66]) (countLit q [-67, -71, -73, -75]) (count1582 q) 2 (meaning1572 q) (meaning1583 q) hs
  change valuationOf q 1572 = false ∨ valuationOf q 1583 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1259 (q : Snake 81) (h : Conditions q) : valuation q 1572 = false ∨ valuation q 1583 = true := counterClause1259 (baseVal q)

theorem counterClause1260 (q : Nat → Bool) : valuationOf q 1572 = false ∨ valuationOf q 1578 = false ∨ valuationOf q 1584 = true := by
  have hs : count1582 q = (countLit q [-63, -64, -66]) + (countLit q [-67, -71, -73, -75]) := List.countP_append (p := literal q) (l₁ := [-63, -64, -66]) (l₂ := [-67, -71, -73, -75])
  have hm := merge_two (literal (valuationOf q) (1572)) (literal (valuationOf q) (1578)) (literal (valuationOf q) (1584)) (countLit q [-63, -64, -66]) (countLit q [-67, -71, -73, -75]) (count1582 q) 2 1 (meaning1572 q) (meaning1578 q) (meaning1584 q) hs
  change valuationOf q 1572 = false ∨ valuationOf q 1578 = false ∨ valuationOf q 1584 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1260 (q : Snake 81) (h : Conditions q) : valuation q 1572 = false ∨ valuation q 1578 = false ∨ valuation q 1584 = true := counterClause1260 (baseVal q)

theorem counterClause1261 (q : Nat → Bool) : valuationOf q 1572 = false ∨ valuationOf q 1579 = false ∨ valuationOf q 1585 = true := by
  have hs : count1582 q = (countLit q [-63, -64, -66]) + (countLit q [-67, -71, -73, -75]) := List.countP_append (p := literal q) (l₁ := [-63, -64, -66]) (l₂ := [-67, -71, -73, -75])
  have hm := merge_two (literal (valuationOf q) (1572)) (literal (valuationOf q) (1579)) (literal (valuationOf q) (1585)) (countLit q [-63, -64, -66]) (countLit q [-67, -71, -73, -75]) (count1582 q) 2 2 (meaning1572 q) (meaning1579 q) (meaning1585 q) hs
  change valuationOf q 1572 = false ∨ valuationOf q 1579 = false ∨ valuationOf q 1585 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1261 (q : Snake 81) (h : Conditions q) : valuation q 1572 = false ∨ valuation q 1579 = false ∨ valuation q 1585 = true := counterClause1261 (baseVal q)

theorem counterClause1262 (q : Nat → Bool) : valuationOf q 1572 = false ∨ valuationOf q 1580 = false ∨ valuationOf q 1586 = true := by
  have hs : count1582 q = (countLit q [-63, -64, -66]) + (countLit q [-67, -71, -73, -75]) := List.countP_append (p := literal q) (l₁ := [-63, -64, -66]) (l₂ := [-67, -71, -73, -75])
  have hm := merge_two (literal (valuationOf q) (1572)) (literal (valuationOf q) (1580)) (literal (valuationOf q) (1586)) (countLit q [-63, -64, -66]) (countLit q [-67, -71, -73, -75]) (count1582 q) 2 3 (meaning1572 q) (meaning1580 q) (meaning1586 q) hs
  change valuationOf q 1572 = false ∨ valuationOf q 1580 = false ∨ valuationOf q 1586 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1262 (q : Snake 81) (h : Conditions q) : valuation q 1572 = false ∨ valuation q 1580 = false ∨ valuation q 1586 = true := counterClause1262 (baseVal q)

theorem counterClause1263 (q : Nat → Bool) : valuationOf q 1572 = false ∨ valuationOf q 1581 = false ∨ valuationOf q 1587 = true := by
  have hs : count1582 q = (countLit q [-63, -64, -66]) + (countLit q [-67, -71, -73, -75]) := List.countP_append (p := literal q) (l₁ := [-63, -64, -66]) (l₂ := [-67, -71, -73, -75])
  have hm := merge_two (literal (valuationOf q) (1572)) (literal (valuationOf q) (1581)) (literal (valuationOf q) (1587)) (countLit q [-63, -64, -66]) (countLit q [-67, -71, -73, -75]) (count1582 q) 2 4 (meaning1572 q) (meaning1581 q) (meaning1587 q) hs
  change valuationOf q 1572 = false ∨ valuationOf q 1581 = false ∨ valuationOf q 1587 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1263 (q : Snake 81) (h : Conditions q) : valuation q 1572 = false ∨ valuation q 1581 = false ∨ valuation q 1587 = true := counterClause1263 (baseVal q)

theorem counterClause1264 (q : Nat → Bool) : valuationOf q 1573 = false ∨ valuationOf q 1584 = true := by
  have hs : count1582 q = (countLit q [-63, -64, -66]) + (countLit q [-67, -71, -73, -75]) := List.countP_append (p := literal q) (l₁ := [-63, -64, -66]) (l₂ := [-67, -71, -73, -75])
  have hm := merge_left (literal (valuationOf q) (1573)) (literal (valuationOf q) (1584)) (countLit q [-63, -64, -66]) (countLit q [-67, -71, -73, -75]) (count1582 q) 3 (meaning1573 q) (meaning1584 q) hs
  change valuationOf q 1573 = false ∨ valuationOf q 1584 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1264 (q : Snake 81) (h : Conditions q) : valuation q 1573 = false ∨ valuation q 1584 = true := counterClause1264 (baseVal q)

theorem counterClause1265 (q : Nat → Bool) : valuationOf q 1573 = false ∨ valuationOf q 1578 = false ∨ valuationOf q 1585 = true := by
  have hs : count1582 q = (countLit q [-63, -64, -66]) + (countLit q [-67, -71, -73, -75]) := List.countP_append (p := literal q) (l₁ := [-63, -64, -66]) (l₂ := [-67, -71, -73, -75])
  have hm := merge_two (literal (valuationOf q) (1573)) (literal (valuationOf q) (1578)) (literal (valuationOf q) (1585)) (countLit q [-63, -64, -66]) (countLit q [-67, -71, -73, -75]) (count1582 q) 3 1 (meaning1573 q) (meaning1578 q) (meaning1585 q) hs
  change valuationOf q 1573 = false ∨ valuationOf q 1578 = false ∨ valuationOf q 1585 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1265 (q : Snake 81) (h : Conditions q) : valuation q 1573 = false ∨ valuation q 1578 = false ∨ valuation q 1585 = true := counterClause1265 (baseVal q)

theorem counterClause1266 (q : Nat → Bool) : valuationOf q 1573 = false ∨ valuationOf q 1579 = false ∨ valuationOf q 1586 = true := by
  have hs : count1582 q = (countLit q [-63, -64, -66]) + (countLit q [-67, -71, -73, -75]) := List.countP_append (p := literal q) (l₁ := [-63, -64, -66]) (l₂ := [-67, -71, -73, -75])
  have hm := merge_two (literal (valuationOf q) (1573)) (literal (valuationOf q) (1579)) (literal (valuationOf q) (1586)) (countLit q [-63, -64, -66]) (countLit q [-67, -71, -73, -75]) (count1582 q) 3 2 (meaning1573 q) (meaning1579 q) (meaning1586 q) hs
  change valuationOf q 1573 = false ∨ valuationOf q 1579 = false ∨ valuationOf q 1586 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1266 (q : Snake 81) (h : Conditions q) : valuation q 1573 = false ∨ valuation q 1579 = false ∨ valuation q 1586 = true := counterClause1266 (baseVal q)

theorem counterClause1267 (q : Nat → Bool) : valuationOf q 82 = true ∨ valuationOf q 1589 = true := by
  have hs : count1589 q = (countLit q [-80]) + (countLit q [-82]) := List.countP_append (p := literal q) (l₁ := [-80]) (l₂ := [-82])
  have hm := merge_right (literal (valuationOf q) (-82)) (literal (valuationOf q) (1589)) (countLit q [-80]) (countLit q [-82]) (count1589 q) 1 (meaningNeg82 q) (meaning1589 q) hs
  change (! (valuationOf q 82)) = false ∨ valuationOf q 1589 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1267 (q : Snake 81) (h : Conditions q) : valuation q 82 = true ∨ valuation q 1589 = true := counterClause1267 (baseVal q)

theorem counterClause1268 (q : Nat → Bool) : valuationOf q 80 = true ∨ valuationOf q 1589 = true := by
  have hs : count1589 q = (countLit q [-80]) + (countLit q [-82]) := List.countP_append (p := literal q) (l₁ := [-80]) (l₂ := [-82])
  have hm := merge_left (literal (valuationOf q) (-80)) (literal (valuationOf q) (1589)) (countLit q [-80]) (countLit q [-82]) (count1589 q) 1 (meaningNeg80 q) (meaning1589 q) hs
  change (! (valuationOf q 80)) = false ∨ valuationOf q 1589 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1268 (q : Snake 81) (h : Conditions q) : valuation q 80 = true ∨ valuation q 1589 = true := counterClause1268 (baseVal q)

theorem counterClause1269 (q : Nat → Bool) : valuationOf q 80 = true ∨ valuationOf q 82 = true ∨ valuationOf q 1590 = true := by
  have hs : count1589 q = (countLit q [-80]) + (countLit q [-82]) := List.countP_append (p := literal q) (l₁ := [-80]) (l₂ := [-82])
  have hm := merge_two (literal (valuationOf q) (-80)) (literal (valuationOf q) (-82)) (literal (valuationOf q) (1590)) (countLit q [-80]) (countLit q [-82]) (count1589 q) 1 1 (meaningNeg80 q) (meaningNeg82 q) (meaning1590 q) hs
  change (! (valuationOf q 80)) = false ∨ (! (valuationOf q 82)) = false ∨ valuationOf q 1590 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1269 (q : Snake 81) (h : Conditions q) : valuation q 80 = true ∨ valuation q 82 = true ∨ valuation q 1590 = true := counterClause1269 (baseVal q)

theorem counterClause1270 (q : Nat → Bool) : valuationOf q 1589 = false ∨ valuationOf q 1591 = true := by
  have hs : count1591 q = (countLit q [-76]) + (countLit q [-80, -82]) := List.countP_append (p := literal q) (l₁ := [-76]) (l₂ := [-80, -82])
  have hm := merge_right (literal (valuationOf q) (1589)) (literal (valuationOf q) (1591)) (countLit q [-76]) (countLit q [-80, -82]) (count1591 q) 1 (meaning1589 q) (meaning1591 q) hs
  change valuationOf q 1589 = false ∨ valuationOf q 1591 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1270 (q : Snake 81) (h : Conditions q) : valuation q 1589 = false ∨ valuation q 1591 = true := counterClause1270 (baseVal q)

theorem counterClause1271 (q : Nat → Bool) : valuationOf q 1590 = false ∨ valuationOf q 1592 = true := by
  have hs : count1591 q = (countLit q [-76]) + (countLit q [-80, -82]) := List.countP_append (p := literal q) (l₁ := [-76]) (l₂ := [-80, -82])
  have hm := merge_right (literal (valuationOf q) (1590)) (literal (valuationOf q) (1592)) (countLit q [-76]) (countLit q [-80, -82]) (count1591 q) 2 (meaning1590 q) (meaning1592 q) hs
  change valuationOf q 1590 = false ∨ valuationOf q 1592 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1271 (q : Snake 81) (h : Conditions q) : valuation q 1590 = false ∨ valuation q 1592 = true := counterClause1271 (baseVal q)

theorem counterClause1272 (q : Nat → Bool) : valuationOf q 76 = true ∨ valuationOf q 1591 = true := by
  have hs : count1591 q = (countLit q [-76]) + (countLit q [-80, -82]) := List.countP_append (p := literal q) (l₁ := [-76]) (l₂ := [-80, -82])
  have hm := merge_left (literal (valuationOf q) (-76)) (literal (valuationOf q) (1591)) (countLit q [-76]) (countLit q [-80, -82]) (count1591 q) 1 (meaningNeg76 q) (meaning1591 q) hs
  change (! (valuationOf q 76)) = false ∨ valuationOf q 1591 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1272 (q : Snake 81) (h : Conditions q) : valuation q 76 = true ∨ valuation q 1591 = true := counterClause1272 (baseVal q)

theorem counterClause1273 (q : Nat → Bool) : valuationOf q 76 = true ∨ valuationOf q 1589 = false ∨ valuationOf q 1592 = true := by
  have hs : count1591 q = (countLit q [-76]) + (countLit q [-80, -82]) := List.countP_append (p := literal q) (l₁ := [-76]) (l₂ := [-80, -82])
  have hm := merge_two (literal (valuationOf q) (-76)) (literal (valuationOf q) (1589)) (literal (valuationOf q) (1592)) (countLit q [-76]) (countLit q [-80, -82]) (count1591 q) 1 1 (meaningNeg76 q) (meaning1589 q) (meaning1592 q) hs
  change (! (valuationOf q 76)) = false ∨ valuationOf q 1589 = false ∨ valuationOf q 1592 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1273 (q : Snake 81) (h : Conditions q) : valuation q 76 = true ∨ valuation q 1589 = false ∨ valuation q 1592 = true := counterClause1273 (baseVal q)

theorem counterClause1274 (q : Nat → Bool) : valuationOf q 76 = true ∨ valuationOf q 1590 = false ∨ valuationOf q 1593 = true := by
  have hs : count1591 q = (countLit q [-76]) + (countLit q [-80, -82]) := List.countP_append (p := literal q) (l₁ := [-76]) (l₂ := [-80, -82])
  have hm := merge_two (literal (valuationOf q) (-76)) (literal (valuationOf q) (1590)) (literal (valuationOf q) (1593)) (countLit q [-76]) (countLit q [-80, -82]) (count1591 q) 1 2 (meaningNeg76 q) (meaning1590 q) (meaning1593 q) hs
  change (! (valuationOf q 76)) = false ∨ valuationOf q 1590 = false ∨ valuationOf q 1593 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1274 (q : Snake 81) (h : Conditions q) : valuation q 76 = true ∨ valuation q 1590 = false ∨ valuation q 1593 = true := counterClause1274 (baseVal q)

theorem counterClause1275 (q : Nat → Bool) : valuationOf q 85 = true ∨ valuationOf q 1594 = true := by
  have hs : count1594 q = (countLit q [-84]) + (countLit q [-85]) := List.countP_append (p := literal q) (l₁ := [-84]) (l₂ := [-85])
  have hm := merge_right (literal (valuationOf q) (-85)) (literal (valuationOf q) (1594)) (countLit q [-84]) (countLit q [-85]) (count1594 q) 1 (meaningNeg85 q) (meaning1594 q) hs
  change (! (valuationOf q 85)) = false ∨ valuationOf q 1594 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1275 (q : Snake 81) (h : Conditions q) : valuation q 85 = true ∨ valuation q 1594 = true := counterClause1275 (baseVal q)

theorem counterClause1276 (q : Nat → Bool) : valuationOf q 84 = true ∨ valuationOf q 1594 = true := by
  have hs : count1594 q = (countLit q [-84]) + (countLit q [-85]) := List.countP_append (p := literal q) (l₁ := [-84]) (l₂ := [-85])
  have hm := merge_left (literal (valuationOf q) (-84)) (literal (valuationOf q) (1594)) (countLit q [-84]) (countLit q [-85]) (count1594 q) 1 (meaningNeg84 q) (meaning1594 q) hs
  change (! (valuationOf q 84)) = false ∨ valuationOf q 1594 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1276 (q : Snake 81) (h : Conditions q) : valuation q 84 = true ∨ valuation q 1594 = true := counterClause1276 (baseVal q)

theorem counterClause1277 (q : Nat → Bool) : valuationOf q 84 = true ∨ valuationOf q 85 = true ∨ valuationOf q 1595 = true := by
  have hs : count1594 q = (countLit q [-84]) + (countLit q [-85]) := List.countP_append (p := literal q) (l₁ := [-84]) (l₂ := [-85])
  have hm := merge_two (literal (valuationOf q) (-84)) (literal (valuationOf q) (-85)) (literal (valuationOf q) (1595)) (countLit q [-84]) (countLit q [-85]) (count1594 q) 1 1 (meaningNeg84 q) (meaningNeg85 q) (meaning1595 q) hs
  change (! (valuationOf q 84)) = false ∨ (! (valuationOf q 85)) = false ∨ valuationOf q 1595 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1277 (q : Snake 81) (h : Conditions q) : valuation q 84 = true ∨ valuation q 85 = true ∨ valuation q 1595 = true := counterClause1277 (baseVal q)

theorem counterClause1278 (q : Nat → Bool) : valuationOf q 91 = true ∨ valuationOf q 1596 = true := by
  have hs : count1596 q = (countLit q [-89]) + (countLit q [-91]) := List.countP_append (p := literal q) (l₁ := [-89]) (l₂ := [-91])
  have hm := merge_right (literal (valuationOf q) (-91)) (literal (valuationOf q) (1596)) (countLit q [-89]) (countLit q [-91]) (count1596 q) 1 (meaningNeg91 q) (meaning1596 q) hs
  change (! (valuationOf q 91)) = false ∨ valuationOf q 1596 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1278 (q : Snake 81) (h : Conditions q) : valuation q 91 = true ∨ valuation q 1596 = true := counterClause1278 (baseVal q)

theorem counterClause1279 (q : Nat → Bool) : valuationOf q 89 = true ∨ valuationOf q 1596 = true := by
  have hs : count1596 q = (countLit q [-89]) + (countLit q [-91]) := List.countP_append (p := literal q) (l₁ := [-89]) (l₂ := [-91])
  have hm := merge_left (literal (valuationOf q) (-89)) (literal (valuationOf q) (1596)) (countLit q [-89]) (countLit q [-91]) (count1596 q) 1 (meaningNeg89 q) (meaning1596 q) hs
  change (! (valuationOf q 89)) = false ∨ valuationOf q 1596 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1279 (q : Snake 81) (h : Conditions q) : valuation q 89 = true ∨ valuation q 1596 = true := counterClause1279 (baseVal q)

theorem counterClause1280 (q : Nat → Bool) : valuationOf q 89 = true ∨ valuationOf q 91 = true ∨ valuationOf q 1597 = true := by
  have hs : count1596 q = (countLit q [-89]) + (countLit q [-91]) := List.countP_append (p := literal q) (l₁ := [-89]) (l₂ := [-91])
  have hm := merge_two (literal (valuationOf q) (-89)) (literal (valuationOf q) (-91)) (literal (valuationOf q) (1597)) (countLit q [-89]) (countLit q [-91]) (count1596 q) 1 1 (meaningNeg89 q) (meaningNeg91 q) (meaning1597 q) hs
  change (! (valuationOf q 89)) = false ∨ (! (valuationOf q 91)) = false ∨ valuationOf q 1597 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1280 (q : Snake 81) (h : Conditions q) : valuation q 89 = true ∨ valuation q 91 = true ∨ valuation q 1597 = true := counterClause1280 (baseVal q)

theorem block39 (q : Snake 81) (h : Conditions q) : B112E047.Block39 (valuation q) :=
  ⟨clause1249 q h, clause1250 q h, clause1251 q h, clause1252 q h, clause1253 q h, clause1254 q h, clause1255 q h, clause1256 q h, clause1257 q h, clause1258 q h, clause1259 q h, clause1260 q h, clause1261 q h, clause1262 q h, clause1263 q h, clause1264 q h, clause1265 q h, clause1266 q h, clause1267 q h, clause1268 q h, clause1269 q h, clause1270 q h, clause1271 q h, clause1272 q h, clause1273 q h, clause1274 q h, clause1275 q h, clause1276 q h, clause1277 q h, clause1278 q h, clause1279 q h, clause1280 q h⟩

end
end Snake9.Regrowth.E112047
