import E112207Semantics
import B112E207Inputs
namespace Snake9.Regrowth.E112207
noncomputable section
local instance blockDec40 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1281 (q : Nat → Bool) : valuationOf q 1583 = false ∨ valuationOf q 1644 = false ∨ valuationOf q 1661 = true := by
  have hs : count1655 q = (countLit q [-62, -63, -66, -69, -71, -72, -74, -75, -79, -80, -81, -82, -86, -89]) + (countLit q [-90, -92, -93, -95, -98, -99, -100, -101, -105, -107, -108, -112, -113, -114, -115]) := List.countP_append (p := literal q) (l₁ := [-62, -63, -66, -69, -71, -72, -74, -75, -79, -80, -81, -82, -86, -89]) (l₂ := [-90, -92, -93, -95, -98, -99, -100, -101, -105, -107, -108, -112, -113, -114, -115])
  have hm := merge_two (literal (valuationOf q) (1583)) (literal (valuationOf q) (1644)) (literal (valuationOf q) (1661)) (countLit q [-62, -63, -66, -69, -71, -72, -74, -75, -79, -80, -81, -82, -86, -89]) (countLit q [-90, -92, -93, -95, -98, -99, -100, -101, -105, -107, -108, -112, -113, -114, -115]) (count1655 q) 2 5 (meaning1583 q) (meaning1644 q) (meaning1661 q) hs
  change valuationOf q 1583 = false ∨ valuationOf q 1644 = false ∨ valuationOf q 1661 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1281 (q : Snake 81) (h : Conditions q) : valuation q 1583 = false ∨ valuation q 1644 = false ∨ valuation q 1661 = true := counterClause1281 (baseVal q)

theorem counterClause1282 (q : Nat → Bool) : valuationOf q 1583 = false ∨ valuationOf q 1645 = false ∨ valuationOf q 1662 = true := by
  have hs : count1655 q = (countLit q [-62, -63, -66, -69, -71, -72, -74, -75, -79, -80, -81, -82, -86, -89]) + (countLit q [-90, -92, -93, -95, -98, -99, -100, -101, -105, -107, -108, -112, -113, -114, -115]) := List.countP_append (p := literal q) (l₁ := [-62, -63, -66, -69, -71, -72, -74, -75, -79, -80, -81, -82, -86, -89]) (l₂ := [-90, -92, -93, -95, -98, -99, -100, -101, -105, -107, -108, -112, -113, -114, -115])
  have hm := merge_two (literal (valuationOf q) (1583)) (literal (valuationOf q) (1645)) (literal (valuationOf q) (1662)) (countLit q [-62, -63, -66, -69, -71, -72, -74, -75, -79, -80, -81, -82, -86, -89]) (countLit q [-90, -92, -93, -95, -98, -99, -100, -101, -105, -107, -108, -112, -113, -114, -115]) (count1655 q) 2 6 (meaning1583 q) (meaning1645 q) (meaning1662 q) hs
  change valuationOf q 1583 = false ∨ valuationOf q 1645 = false ∨ valuationOf q 1662 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1282 (q : Snake 81) (h : Conditions q) : valuation q 1583 = false ∨ valuation q 1645 = false ∨ valuation q 1662 = true := counterClause1282 (baseVal q)

theorem counterClause1283 (q : Nat → Bool) : valuationOf q 1584 = false ∨ valuationOf q 1641 = false ∨ valuationOf q 1659 = true := by
  have hs : count1655 q = (countLit q [-62, -63, -66, -69, -71, -72, -74, -75, -79, -80, -81, -82, -86, -89]) + (countLit q [-90, -92, -93, -95, -98, -99, -100, -101, -105, -107, -108, -112, -113, -114, -115]) := List.countP_append (p := literal q) (l₁ := [-62, -63, -66, -69, -71, -72, -74, -75, -79, -80, -81, -82, -86, -89]) (l₂ := [-90, -92, -93, -95, -98, -99, -100, -101, -105, -107, -108, -112, -113, -114, -115])
  have hm := merge_two (literal (valuationOf q) (1584)) (literal (valuationOf q) (1641)) (literal (valuationOf q) (1659)) (countLit q [-62, -63, -66, -69, -71, -72, -74, -75, -79, -80, -81, -82, -86, -89]) (countLit q [-90, -92, -93, -95, -98, -99, -100, -101, -105, -107, -108, -112, -113, -114, -115]) (count1655 q) 3 2 (meaning1584 q) (meaning1641 q) (meaning1659 q) hs
  change valuationOf q 1584 = false ∨ valuationOf q 1641 = false ∨ valuationOf q 1659 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1283 (q : Snake 81) (h : Conditions q) : valuation q 1584 = false ∨ valuation q 1641 = false ∨ valuation q 1659 = true := counterClause1283 (baseVal q)

theorem counterClause1284 (q : Nat → Bool) : valuationOf q 1584 = false ∨ valuationOf q 1642 = false ∨ valuationOf q 1660 = true := by
  have hs : count1655 q = (countLit q [-62, -63, -66, -69, -71, -72, -74, -75, -79, -80, -81, -82, -86, -89]) + (countLit q [-90, -92, -93, -95, -98, -99, -100, -101, -105, -107, -108, -112, -113, -114, -115]) := List.countP_append (p := literal q) (l₁ := [-62, -63, -66, -69, -71, -72, -74, -75, -79, -80, -81, -82, -86, -89]) (l₂ := [-90, -92, -93, -95, -98, -99, -100, -101, -105, -107, -108, -112, -113, -114, -115])
  have hm := merge_two (literal (valuationOf q) (1584)) (literal (valuationOf q) (1642)) (literal (valuationOf q) (1660)) (countLit q [-62, -63, -66, -69, -71, -72, -74, -75, -79, -80, -81, -82, -86, -89]) (countLit q [-90, -92, -93, -95, -98, -99, -100, -101, -105, -107, -108, -112, -113, -114, -115]) (count1655 q) 3 3 (meaning1584 q) (meaning1642 q) (meaning1660 q) hs
  change valuationOf q 1584 = false ∨ valuationOf q 1642 = false ∨ valuationOf q 1660 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1284 (q : Snake 81) (h : Conditions q) : valuation q 1584 = false ∨ valuation q 1642 = false ∨ valuation q 1660 = true := counterClause1284 (baseVal q)

theorem counterClause1285 (q : Nat → Bool) : valuationOf q 1584 = false ∨ valuationOf q 1643 = false ∨ valuationOf q 1661 = true := by
  have hs : count1655 q = (countLit q [-62, -63, -66, -69, -71, -72, -74, -75, -79, -80, -81, -82, -86, -89]) + (countLit q [-90, -92, -93, -95, -98, -99, -100, -101, -105, -107, -108, -112, -113, -114, -115]) := List.countP_append (p := literal q) (l₁ := [-62, -63, -66, -69, -71, -72, -74, -75, -79, -80, -81, -82, -86, -89]) (l₂ := [-90, -92, -93, -95, -98, -99, -100, -101, -105, -107, -108, -112, -113, -114, -115])
  have hm := merge_two (literal (valuationOf q) (1584)) (literal (valuationOf q) (1643)) (literal (valuationOf q) (1661)) (countLit q [-62, -63, -66, -69, -71, -72, -74, -75, -79, -80, -81, -82, -86, -89]) (countLit q [-90, -92, -93, -95, -98, -99, -100, -101, -105, -107, -108, -112, -113, -114, -115]) (count1655 q) 3 4 (meaning1584 q) (meaning1643 q) (meaning1661 q) hs
  change valuationOf q 1584 = false ∨ valuationOf q 1643 = false ∨ valuationOf q 1661 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1285 (q : Snake 81) (h : Conditions q) : valuation q 1584 = false ∨ valuation q 1643 = false ∨ valuation q 1661 = true := counterClause1285 (baseVal q)

theorem counterClause1286 (q : Nat → Bool) : valuationOf q 1584 = false ∨ valuationOf q 1644 = false ∨ valuationOf q 1662 = true := by
  have hs : count1655 q = (countLit q [-62, -63, -66, -69, -71, -72, -74, -75, -79, -80, -81, -82, -86, -89]) + (countLit q [-90, -92, -93, -95, -98, -99, -100, -101, -105, -107, -108, -112, -113, -114, -115]) := List.countP_append (p := literal q) (l₁ := [-62, -63, -66, -69, -71, -72, -74, -75, -79, -80, -81, -82, -86, -89]) (l₂ := [-90, -92, -93, -95, -98, -99, -100, -101, -105, -107, -108, -112, -113, -114, -115])
  have hm := merge_two (literal (valuationOf q) (1584)) (literal (valuationOf q) (1644)) (literal (valuationOf q) (1662)) (countLit q [-62, -63, -66, -69, -71, -72, -74, -75, -79, -80, -81, -82, -86, -89]) (countLit q [-90, -92, -93, -95, -98, -99, -100, -101, -105, -107, -108, -112, -113, -114, -115]) (count1655 q) 3 5 (meaning1584 q) (meaning1644 q) (meaning1662 q) hs
  change valuationOf q 1584 = false ∨ valuationOf q 1644 = false ∨ valuationOf q 1662 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1286 (q : Snake 81) (h : Conditions q) : valuation q 1584 = false ∨ valuation q 1644 = false ∨ valuation q 1662 = true := counterClause1286 (baseVal q)

theorem counterClause1287 (q : Nat → Bool) : valuationOf q 1584 = false ∨ valuationOf q 1645 = false ∨ valuationOf q 1663 = true := by
  have hs : count1655 q = (countLit q [-62, -63, -66, -69, -71, -72, -74, -75, -79, -80, -81, -82, -86, -89]) + (countLit q [-90, -92, -93, -95, -98, -99, -100, -101, -105, -107, -108, -112, -113, -114, -115]) := List.countP_append (p := literal q) (l₁ := [-62, -63, -66, -69, -71, -72, -74, -75, -79, -80, -81, -82, -86, -89]) (l₂ := [-90, -92, -93, -95, -98, -99, -100, -101, -105, -107, -108, -112, -113, -114, -115])
  have hm := merge_two (literal (valuationOf q) (1584)) (literal (valuationOf q) (1645)) (literal (valuationOf q) (1663)) (countLit q [-62, -63, -66, -69, -71, -72, -74, -75, -79, -80, -81, -82, -86, -89]) (countLit q [-90, -92, -93, -95, -98, -99, -100, -101, -105, -107, -108, -112, -113, -114, -115]) (count1655 q) 3 6 (meaning1584 q) (meaning1645 q) (meaning1663 q) hs
  change valuationOf q 1584 = false ∨ valuationOf q 1645 = false ∨ valuationOf q 1663 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1287 (q : Snake 81) (h : Conditions q) : valuation q 1584 = false ∨ valuation q 1645 = false ∨ valuation q 1663 = true := counterClause1287 (baseVal q)

theorem counterClause1288 (q : Nat → Bool) : valuationOf q 1585 = false ∨ valuationOf q 1640 = false ∨ valuationOf q 1659 = true := by
  have hs : count1655 q = (countLit q [-62, -63, -66, -69, -71, -72, -74, -75, -79, -80, -81, -82, -86, -89]) + (countLit q [-90, -92, -93, -95, -98, -99, -100, -101, -105, -107, -108, -112, -113, -114, -115]) := List.countP_append (p := literal q) (l₁ := [-62, -63, -66, -69, -71, -72, -74, -75, -79, -80, -81, -82, -86, -89]) (l₂ := [-90, -92, -93, -95, -98, -99, -100, -101, -105, -107, -108, -112, -113, -114, -115])
  have hm := merge_two (literal (valuationOf q) (1585)) (literal (valuationOf q) (1640)) (literal (valuationOf q) (1659)) (countLit q [-62, -63, -66, -69, -71, -72, -74, -75, -79, -80, -81, -82, -86, -89]) (countLit q [-90, -92, -93, -95, -98, -99, -100, -101, -105, -107, -108, -112, -113, -114, -115]) (count1655 q) 4 1 (meaning1585 q) (meaning1640 q) (meaning1659 q) hs
  change valuationOf q 1585 = false ∨ valuationOf q 1640 = false ∨ valuationOf q 1659 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1288 (q : Snake 81) (h : Conditions q) : valuation q 1585 = false ∨ valuation q 1640 = false ∨ valuation q 1659 = true := counterClause1288 (baseVal q)

theorem counterClause1289 (q : Nat → Bool) : valuationOf q 1585 = false ∨ valuationOf q 1641 = false ∨ valuationOf q 1660 = true := by
  have hs : count1655 q = (countLit q [-62, -63, -66, -69, -71, -72, -74, -75, -79, -80, -81, -82, -86, -89]) + (countLit q [-90, -92, -93, -95, -98, -99, -100, -101, -105, -107, -108, -112, -113, -114, -115]) := List.countP_append (p := literal q) (l₁ := [-62, -63, -66, -69, -71, -72, -74, -75, -79, -80, -81, -82, -86, -89]) (l₂ := [-90, -92, -93, -95, -98, -99, -100, -101, -105, -107, -108, -112, -113, -114, -115])
  have hm := merge_two (literal (valuationOf q) (1585)) (literal (valuationOf q) (1641)) (literal (valuationOf q) (1660)) (countLit q [-62, -63, -66, -69, -71, -72, -74, -75, -79, -80, -81, -82, -86, -89]) (countLit q [-90, -92, -93, -95, -98, -99, -100, -101, -105, -107, -108, -112, -113, -114, -115]) (count1655 q) 4 2 (meaning1585 q) (meaning1641 q) (meaning1660 q) hs
  change valuationOf q 1585 = false ∨ valuationOf q 1641 = false ∨ valuationOf q 1660 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1289 (q : Snake 81) (h : Conditions q) : valuation q 1585 = false ∨ valuation q 1641 = false ∨ valuation q 1660 = true := counterClause1289 (baseVal q)

theorem counterClause1290 (q : Nat → Bool) : valuationOf q 1585 = false ∨ valuationOf q 1642 = false ∨ valuationOf q 1661 = true := by
  have hs : count1655 q = (countLit q [-62, -63, -66, -69, -71, -72, -74, -75, -79, -80, -81, -82, -86, -89]) + (countLit q [-90, -92, -93, -95, -98, -99, -100, -101, -105, -107, -108, -112, -113, -114, -115]) := List.countP_append (p := literal q) (l₁ := [-62, -63, -66, -69, -71, -72, -74, -75, -79, -80, -81, -82, -86, -89]) (l₂ := [-90, -92, -93, -95, -98, -99, -100, -101, -105, -107, -108, -112, -113, -114, -115])
  have hm := merge_two (literal (valuationOf q) (1585)) (literal (valuationOf q) (1642)) (literal (valuationOf q) (1661)) (countLit q [-62, -63, -66, -69, -71, -72, -74, -75, -79, -80, -81, -82, -86, -89]) (countLit q [-90, -92, -93, -95, -98, -99, -100, -101, -105, -107, -108, -112, -113, -114, -115]) (count1655 q) 4 3 (meaning1585 q) (meaning1642 q) (meaning1661 q) hs
  change valuationOf q 1585 = false ∨ valuationOf q 1642 = false ∨ valuationOf q 1661 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1290 (q : Snake 81) (h : Conditions q) : valuation q 1585 = false ∨ valuation q 1642 = false ∨ valuation q 1661 = true := counterClause1290 (baseVal q)

theorem counterClause1291 (q : Nat → Bool) : valuationOf q 1585 = false ∨ valuationOf q 1643 = false ∨ valuationOf q 1662 = true := by
  have hs : count1655 q = (countLit q [-62, -63, -66, -69, -71, -72, -74, -75, -79, -80, -81, -82, -86, -89]) + (countLit q [-90, -92, -93, -95, -98, -99, -100, -101, -105, -107, -108, -112, -113, -114, -115]) := List.countP_append (p := literal q) (l₁ := [-62, -63, -66, -69, -71, -72, -74, -75, -79, -80, -81, -82, -86, -89]) (l₂ := [-90, -92, -93, -95, -98, -99, -100, -101, -105, -107, -108, -112, -113, -114, -115])
  have hm := merge_two (literal (valuationOf q) (1585)) (literal (valuationOf q) (1643)) (literal (valuationOf q) (1662)) (countLit q [-62, -63, -66, -69, -71, -72, -74, -75, -79, -80, -81, -82, -86, -89]) (countLit q [-90, -92, -93, -95, -98, -99, -100, -101, -105, -107, -108, -112, -113, -114, -115]) (count1655 q) 4 4 (meaning1585 q) (meaning1643 q) (meaning1662 q) hs
  change valuationOf q 1585 = false ∨ valuationOf q 1643 = false ∨ valuationOf q 1662 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1291 (q : Snake 81) (h : Conditions q) : valuation q 1585 = false ∨ valuation q 1643 = false ∨ valuation q 1662 = true := counterClause1291 (baseVal q)

theorem counterClause1292 (q : Nat → Bool) : valuationOf q 1585 = false ∨ valuationOf q 1644 = false ∨ valuationOf q 1663 = true := by
  have hs : count1655 q = (countLit q [-62, -63, -66, -69, -71, -72, -74, -75, -79, -80, -81, -82, -86, -89]) + (countLit q [-90, -92, -93, -95, -98, -99, -100, -101, -105, -107, -108, -112, -113, -114, -115]) := List.countP_append (p := literal q) (l₁ := [-62, -63, -66, -69, -71, -72, -74, -75, -79, -80, -81, -82, -86, -89]) (l₂ := [-90, -92, -93, -95, -98, -99, -100, -101, -105, -107, -108, -112, -113, -114, -115])
  have hm := merge_two (literal (valuationOf q) (1585)) (literal (valuationOf q) (1644)) (literal (valuationOf q) (1663)) (countLit q [-62, -63, -66, -69, -71, -72, -74, -75, -79, -80, -81, -82, -86, -89]) (countLit q [-90, -92, -93, -95, -98, -99, -100, -101, -105, -107, -108, -112, -113, -114, -115]) (count1655 q) 4 5 (meaning1585 q) (meaning1644 q) (meaning1663 q) hs
  change valuationOf q 1585 = false ∨ valuationOf q 1644 = false ∨ valuationOf q 1663 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1292 (q : Snake 81) (h : Conditions q) : valuation q 1585 = false ∨ valuation q 1644 = false ∨ valuation q 1663 = true := counterClause1292 (baseVal q)

theorem counterClause1293 (q : Nat → Bool) : valuationOf q 1585 = false ∨ valuationOf q 1645 = false ∨ valuationOf q 1664 = true := by
  have hs : count1655 q = (countLit q [-62, -63, -66, -69, -71, -72, -74, -75, -79, -80, -81, -82, -86, -89]) + (countLit q [-90, -92, -93, -95, -98, -99, -100, -101, -105, -107, -108, -112, -113, -114, -115]) := List.countP_append (p := literal q) (l₁ := [-62, -63, -66, -69, -71, -72, -74, -75, -79, -80, -81, -82, -86, -89]) (l₂ := [-90, -92, -93, -95, -98, -99, -100, -101, -105, -107, -108, -112, -113, -114, -115])
  have hm := merge_two (literal (valuationOf q) (1585)) (literal (valuationOf q) (1645)) (literal (valuationOf q) (1664)) (countLit q [-62, -63, -66, -69, -71, -72, -74, -75, -79, -80, -81, -82, -86, -89]) (countLit q [-90, -92, -93, -95, -98, -99, -100, -101, -105, -107, -108, -112, -113, -114, -115]) (count1655 q) 4 6 (meaning1585 q) (meaning1645 q) (meaning1664 q) hs
  change valuationOf q 1585 = false ∨ valuationOf q 1645 = false ∨ valuationOf q 1664 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1293 (q : Snake 81) (h : Conditions q) : valuation q 1585 = false ∨ valuation q 1645 = false ∨ valuation q 1664 = true := counterClause1293 (baseVal q)

theorem counterClause1294 (q : Nat → Bool) : valuationOf q 1586 = false ∨ valuationOf q 1640 = false ∨ valuationOf q 1660 = true := by
  have hs : count1655 q = (countLit q [-62, -63, -66, -69, -71, -72, -74, -75, -79, -80, -81, -82, -86, -89]) + (countLit q [-90, -92, -93, -95, -98, -99, -100, -101, -105, -107, -108, -112, -113, -114, -115]) := List.countP_append (p := literal q) (l₁ := [-62, -63, -66, -69, -71, -72, -74, -75, -79, -80, -81, -82, -86, -89]) (l₂ := [-90, -92, -93, -95, -98, -99, -100, -101, -105, -107, -108, -112, -113, -114, -115])
  have hm := merge_two (literal (valuationOf q) (1586)) (literal (valuationOf q) (1640)) (literal (valuationOf q) (1660)) (countLit q [-62, -63, -66, -69, -71, -72, -74, -75, -79, -80, -81, -82, -86, -89]) (countLit q [-90, -92, -93, -95, -98, -99, -100, -101, -105, -107, -108, -112, -113, -114, -115]) (count1655 q) 5 1 (meaning1586 q) (meaning1640 q) (meaning1660 q) hs
  change valuationOf q 1586 = false ∨ valuationOf q 1640 = false ∨ valuationOf q 1660 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1294 (q : Snake 81) (h : Conditions q) : valuation q 1586 = false ∨ valuation q 1640 = false ∨ valuation q 1660 = true := counterClause1294 (baseVal q)

theorem counterClause1295 (q : Nat → Bool) : valuationOf q 1586 = false ∨ valuationOf q 1641 = false ∨ valuationOf q 1661 = true := by
  have hs : count1655 q = (countLit q [-62, -63, -66, -69, -71, -72, -74, -75, -79, -80, -81, -82, -86, -89]) + (countLit q [-90, -92, -93, -95, -98, -99, -100, -101, -105, -107, -108, -112, -113, -114, -115]) := List.countP_append (p := literal q) (l₁ := [-62, -63, -66, -69, -71, -72, -74, -75, -79, -80, -81, -82, -86, -89]) (l₂ := [-90, -92, -93, -95, -98, -99, -100, -101, -105, -107, -108, -112, -113, -114, -115])
  have hm := merge_two (literal (valuationOf q) (1586)) (literal (valuationOf q) (1641)) (literal (valuationOf q) (1661)) (countLit q [-62, -63, -66, -69, -71, -72, -74, -75, -79, -80, -81, -82, -86, -89]) (countLit q [-90, -92, -93, -95, -98, -99, -100, -101, -105, -107, -108, -112, -113, -114, -115]) (count1655 q) 5 2 (meaning1586 q) (meaning1641 q) (meaning1661 q) hs
  change valuationOf q 1586 = false ∨ valuationOf q 1641 = false ∨ valuationOf q 1661 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1295 (q : Snake 81) (h : Conditions q) : valuation q 1586 = false ∨ valuation q 1641 = false ∨ valuation q 1661 = true := counterClause1295 (baseVal q)

theorem counterClause1296 (q : Nat → Bool) : valuationOf q 1586 = false ∨ valuationOf q 1642 = false ∨ valuationOf q 1662 = true := by
  have hs : count1655 q = (countLit q [-62, -63, -66, -69, -71, -72, -74, -75, -79, -80, -81, -82, -86, -89]) + (countLit q [-90, -92, -93, -95, -98, -99, -100, -101, -105, -107, -108, -112, -113, -114, -115]) := List.countP_append (p := literal q) (l₁ := [-62, -63, -66, -69, -71, -72, -74, -75, -79, -80, -81, -82, -86, -89]) (l₂ := [-90, -92, -93, -95, -98, -99, -100, -101, -105, -107, -108, -112, -113, -114, -115])
  have hm := merge_two (literal (valuationOf q) (1586)) (literal (valuationOf q) (1642)) (literal (valuationOf q) (1662)) (countLit q [-62, -63, -66, -69, -71, -72, -74, -75, -79, -80, -81, -82, -86, -89]) (countLit q [-90, -92, -93, -95, -98, -99, -100, -101, -105, -107, -108, -112, -113, -114, -115]) (count1655 q) 5 3 (meaning1586 q) (meaning1642 q) (meaning1662 q) hs
  change valuationOf q 1586 = false ∨ valuationOf q 1642 = false ∨ valuationOf q 1662 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1296 (q : Snake 81) (h : Conditions q) : valuation q 1586 = false ∨ valuation q 1642 = false ∨ valuation q 1662 = true := counterClause1296 (baseVal q)

theorem counterClause1297 (q : Nat → Bool) : valuationOf q 1586 = false ∨ valuationOf q 1643 = false ∨ valuationOf q 1663 = true := by
  have hs : count1655 q = (countLit q [-62, -63, -66, -69, -71, -72, -74, -75, -79, -80, -81, -82, -86, -89]) + (countLit q [-90, -92, -93, -95, -98, -99, -100, -101, -105, -107, -108, -112, -113, -114, -115]) := List.countP_append (p := literal q) (l₁ := [-62, -63, -66, -69, -71, -72, -74, -75, -79, -80, -81, -82, -86, -89]) (l₂ := [-90, -92, -93, -95, -98, -99, -100, -101, -105, -107, -108, -112, -113, -114, -115])
  have hm := merge_two (literal (valuationOf q) (1586)) (literal (valuationOf q) (1643)) (literal (valuationOf q) (1663)) (countLit q [-62, -63, -66, -69, -71, -72, -74, -75, -79, -80, -81, -82, -86, -89]) (countLit q [-90, -92, -93, -95, -98, -99, -100, -101, -105, -107, -108, -112, -113, -114, -115]) (count1655 q) 5 4 (meaning1586 q) (meaning1643 q) (meaning1663 q) hs
  change valuationOf q 1586 = false ∨ valuationOf q 1643 = false ∨ valuationOf q 1663 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1297 (q : Snake 81) (h : Conditions q) : valuation q 1586 = false ∨ valuation q 1643 = false ∨ valuation q 1663 = true := counterClause1297 (baseVal q)

theorem counterClause1298 (q : Nat → Bool) : valuationOf q 1586 = false ∨ valuationOf q 1644 = false ∨ valuationOf q 1664 = true := by
  have hs : count1655 q = (countLit q [-62, -63, -66, -69, -71, -72, -74, -75, -79, -80, -81, -82, -86, -89]) + (countLit q [-90, -92, -93, -95, -98, -99, -100, -101, -105, -107, -108, -112, -113, -114, -115]) := List.countP_append (p := literal q) (l₁ := [-62, -63, -66, -69, -71, -72, -74, -75, -79, -80, -81, -82, -86, -89]) (l₂ := [-90, -92, -93, -95, -98, -99, -100, -101, -105, -107, -108, -112, -113, -114, -115])
  have hm := merge_two (literal (valuationOf q) (1586)) (literal (valuationOf q) (1644)) (literal (valuationOf q) (1664)) (countLit q [-62, -63, -66, -69, -71, -72, -74, -75, -79, -80, -81, -82, -86, -89]) (countLit q [-90, -92, -93, -95, -98, -99, -100, -101, -105, -107, -108, -112, -113, -114, -115]) (count1655 q) 5 5 (meaning1586 q) (meaning1644 q) (meaning1664 q) hs
  change valuationOf q 1586 = false ∨ valuationOf q 1644 = false ∨ valuationOf q 1664 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1298 (q : Snake 81) (h : Conditions q) : valuation q 1586 = false ∨ valuation q 1644 = false ∨ valuation q 1664 = true := counterClause1298 (baseVal q)

theorem counterClause1299 (q : Nat → Bool) : valuationOf q 1587 = false ∨ valuationOf q 1640 = false ∨ valuationOf q 1661 = true := by
  have hs : count1655 q = (countLit q [-62, -63, -66, -69, -71, -72, -74, -75, -79, -80, -81, -82, -86, -89]) + (countLit q [-90, -92, -93, -95, -98, -99, -100, -101, -105, -107, -108, -112, -113, -114, -115]) := List.countP_append (p := literal q) (l₁ := [-62, -63, -66, -69, -71, -72, -74, -75, -79, -80, -81, -82, -86, -89]) (l₂ := [-90, -92, -93, -95, -98, -99, -100, -101, -105, -107, -108, -112, -113, -114, -115])
  have hm := merge_two (literal (valuationOf q) (1587)) (literal (valuationOf q) (1640)) (literal (valuationOf q) (1661)) (countLit q [-62, -63, -66, -69, -71, -72, -74, -75, -79, -80, -81, -82, -86, -89]) (countLit q [-90, -92, -93, -95, -98, -99, -100, -101, -105, -107, -108, -112, -113, -114, -115]) (count1655 q) 6 1 (meaning1587 q) (meaning1640 q) (meaning1661 q) hs
  change valuationOf q 1587 = false ∨ valuationOf q 1640 = false ∨ valuationOf q 1661 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1299 (q : Snake 81) (h : Conditions q) : valuation q 1587 = false ∨ valuation q 1640 = false ∨ valuation q 1661 = true := counterClause1299 (baseVal q)

theorem counterClause1300 (q : Nat → Bool) : valuationOf q 1587 = false ∨ valuationOf q 1641 = false ∨ valuationOf q 1662 = true := by
  have hs : count1655 q = (countLit q [-62, -63, -66, -69, -71, -72, -74, -75, -79, -80, -81, -82, -86, -89]) + (countLit q [-90, -92, -93, -95, -98, -99, -100, -101, -105, -107, -108, -112, -113, -114, -115]) := List.countP_append (p := literal q) (l₁ := [-62, -63, -66, -69, -71, -72, -74, -75, -79, -80, -81, -82, -86, -89]) (l₂ := [-90, -92, -93, -95, -98, -99, -100, -101, -105, -107, -108, -112, -113, -114, -115])
  have hm := merge_two (literal (valuationOf q) (1587)) (literal (valuationOf q) (1641)) (literal (valuationOf q) (1662)) (countLit q [-62, -63, -66, -69, -71, -72, -74, -75, -79, -80, -81, -82, -86, -89]) (countLit q [-90, -92, -93, -95, -98, -99, -100, -101, -105, -107, -108, -112, -113, -114, -115]) (count1655 q) 6 2 (meaning1587 q) (meaning1641 q) (meaning1662 q) hs
  change valuationOf q 1587 = false ∨ valuationOf q 1641 = false ∨ valuationOf q 1662 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1300 (q : Snake 81) (h : Conditions q) : valuation q 1587 = false ∨ valuation q 1641 = false ∨ valuation q 1662 = true := counterClause1300 (baseVal q)

theorem counterClause1301 (q : Nat → Bool) : valuationOf q 1587 = false ∨ valuationOf q 1642 = false ∨ valuationOf q 1663 = true := by
  have hs : count1655 q = (countLit q [-62, -63, -66, -69, -71, -72, -74, -75, -79, -80, -81, -82, -86, -89]) + (countLit q [-90, -92, -93, -95, -98, -99, -100, -101, -105, -107, -108, -112, -113, -114, -115]) := List.countP_append (p := literal q) (l₁ := [-62, -63, -66, -69, -71, -72, -74, -75, -79, -80, -81, -82, -86, -89]) (l₂ := [-90, -92, -93, -95, -98, -99, -100, -101, -105, -107, -108, -112, -113, -114, -115])
  have hm := merge_two (literal (valuationOf q) (1587)) (literal (valuationOf q) (1642)) (literal (valuationOf q) (1663)) (countLit q [-62, -63, -66, -69, -71, -72, -74, -75, -79, -80, -81, -82, -86, -89]) (countLit q [-90, -92, -93, -95, -98, -99, -100, -101, -105, -107, -108, -112, -113, -114, -115]) (count1655 q) 6 3 (meaning1587 q) (meaning1642 q) (meaning1663 q) hs
  change valuationOf q 1587 = false ∨ valuationOf q 1642 = false ∨ valuationOf q 1663 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1301 (q : Snake 81) (h : Conditions q) : valuation q 1587 = false ∨ valuation q 1642 = false ∨ valuation q 1663 = true := counterClause1301 (baseVal q)

theorem counterClause1302 (q : Nat → Bool) : valuationOf q 1587 = false ∨ valuationOf q 1643 = false ∨ valuationOf q 1664 = true := by
  have hs : count1655 q = (countLit q [-62, -63, -66, -69, -71, -72, -74, -75, -79, -80, -81, -82, -86, -89]) + (countLit q [-90, -92, -93, -95, -98, -99, -100, -101, -105, -107, -108, -112, -113, -114, -115]) := List.countP_append (p := literal q) (l₁ := [-62, -63, -66, -69, -71, -72, -74, -75, -79, -80, -81, -82, -86, -89]) (l₂ := [-90, -92, -93, -95, -98, -99, -100, -101, -105, -107, -108, -112, -113, -114, -115])
  have hm := merge_two (literal (valuationOf q) (1587)) (literal (valuationOf q) (1643)) (literal (valuationOf q) (1664)) (countLit q [-62, -63, -66, -69, -71, -72, -74, -75, -79, -80, -81, -82, -86, -89]) (countLit q [-90, -92, -93, -95, -98, -99, -100, -101, -105, -107, -108, -112, -113, -114, -115]) (count1655 q) 6 4 (meaning1587 q) (meaning1643 q) (meaning1664 q) hs
  change valuationOf q 1587 = false ∨ valuationOf q 1643 = false ∨ valuationOf q 1664 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1302 (q : Snake 81) (h : Conditions q) : valuation q 1587 = false ∨ valuation q 1643 = false ∨ valuation q 1664 = true := counterClause1302 (baseVal q)

theorem counterClause1303 (q : Nat → Bool) : valuationOf q 1588 = false ∨ valuationOf q 1641 = false ∨ valuationOf q 1663 = true := by
  have hs : count1655 q = (countLit q [-62, -63, -66, -69, -71, -72, -74, -75, -79, -80, -81, -82, -86, -89]) + (countLit q [-90, -92, -93, -95, -98, -99, -100, -101, -105, -107, -108, -112, -113, -114, -115]) := List.countP_append (p := literal q) (l₁ := [-62, -63, -66, -69, -71, -72, -74, -75, -79, -80, -81, -82, -86, -89]) (l₂ := [-90, -92, -93, -95, -98, -99, -100, -101, -105, -107, -108, -112, -113, -114, -115])
  have hm := merge_two (literal (valuationOf q) (1588)) (literal (valuationOf q) (1641)) (literal (valuationOf q) (1663)) (countLit q [-62, -63, -66, -69, -71, -72, -74, -75, -79, -80, -81, -82, -86, -89]) (countLit q [-90, -92, -93, -95, -98, -99, -100, -101, -105, -107, -108, -112, -113, -114, -115]) (count1655 q) 7 2 (meaning1588 q) (meaning1641 q) (meaning1663 q) hs
  change valuationOf q 1588 = false ∨ valuationOf q 1641 = false ∨ valuationOf q 1663 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1303 (q : Snake 81) (h : Conditions q) : valuation q 1588 = false ∨ valuation q 1641 = false ∨ valuation q 1663 = true := counterClause1303 (baseVal q)

theorem counterClause1304 (q : Nat → Bool) : valuationOf q 1588 = false ∨ valuationOf q 1642 = false ∨ valuationOf q 1664 = true := by
  have hs : count1655 q = (countLit q [-62, -63, -66, -69, -71, -72, -74, -75, -79, -80, -81, -82, -86, -89]) + (countLit q [-90, -92, -93, -95, -98, -99, -100, -101, -105, -107, -108, -112, -113, -114, -115]) := List.countP_append (p := literal q) (l₁ := [-62, -63, -66, -69, -71, -72, -74, -75, -79, -80, -81, -82, -86, -89]) (l₂ := [-90, -92, -93, -95, -98, -99, -100, -101, -105, -107, -108, -112, -113, -114, -115])
  have hm := merge_two (literal (valuationOf q) (1588)) (literal (valuationOf q) (1642)) (literal (valuationOf q) (1664)) (countLit q [-62, -63, -66, -69, -71, -72, -74, -75, -79, -80, -81, -82, -86, -89]) (countLit q [-90, -92, -93, -95, -98, -99, -100, -101, -105, -107, -108, -112, -113, -114, -115]) (count1655 q) 7 3 (meaning1588 q) (meaning1642 q) (meaning1664 q) hs
  change valuationOf q 1588 = false ∨ valuationOf q 1642 = false ∨ valuationOf q 1664 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1304 (q : Snake 81) (h : Conditions q) : valuation q 1588 = false ∨ valuation q 1642 = false ∨ valuation q 1664 = true := counterClause1304 (baseVal q)

theorem counterClause1305 (q : Nat → Bool) : valuationOf q 1588 = false ∨ valuationOf q 1643 = false ∨ valuationOf q 1665 = true := by
  have hs : count1655 q = (countLit q [-62, -63, -66, -69, -71, -72, -74, -75, -79, -80, -81, -82, -86, -89]) + (countLit q [-90, -92, -93, -95, -98, -99, -100, -101, -105, -107, -108, -112, -113, -114, -115]) := List.countP_append (p := literal q) (l₁ := [-62, -63, -66, -69, -71, -72, -74, -75, -79, -80, -81, -82, -86, -89]) (l₂ := [-90, -92, -93, -95, -98, -99, -100, -101, -105, -107, -108, -112, -113, -114, -115])
  have hm := merge_two (literal (valuationOf q) (1588)) (literal (valuationOf q) (1643)) (literal (valuationOf q) (1665)) (countLit q [-62, -63, -66, -69, -71, -72, -74, -75, -79, -80, -81, -82, -86, -89]) (countLit q [-90, -92, -93, -95, -98, -99, -100, -101, -105, -107, -108, -112, -113, -114, -115]) (count1655 q) 7 4 (meaning1588 q) (meaning1643 q) (meaning1665 q) hs
  change valuationOf q 1588 = false ∨ valuationOf q 1643 = false ∨ valuationOf q 1665 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1305 (q : Snake 81) (h : Conditions q) : valuation q 1588 = false ∨ valuation q 1643 = false ∨ valuation q 1665 = true := counterClause1305 (baseVal q)

theorem counterClause1306 (q : Nat → Bool) : valuationOf q 1530 = false ∨ valuationOf q 1665 = false ∨ valuationOf q 1690 = true := by
  have hs : count1673 q = (countLit q [-2, -4, -5, -6, -10, -11, -12, -15, -18, -21, -22, -23, -25, -27, -30, -31, -35, -37, -38, -39, -43, -45, -49, -50, -53, -55, -57, -58, -60]) + (countLit q [-62, -63, -66, -69, -71, -72, -74, -75, -79, -80, -81, -82, -86, -89, -90, -92, -93, -95, -98, -99, -100, -101, -105, -107, -108, -112, -113, -114, -115]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5, -6, -10, -11, -12, -15, -18, -21, -22, -23, -25, -27, -30, -31, -35, -37, -38, -39, -43, -45, -49, -50, -53, -55, -57, -58, -60]) (l₂ := [-62, -63, -66, -69, -71, -72, -74, -75, -79, -80, -81, -82, -86, -89, -90, -92, -93, -95, -98, -99, -100, -101, -105, -107, -108, -112, -113, -114, -115])
  have hm := merge_two (literal (valuationOf q) (1530)) (literal (valuationOf q) (1665)) (literal (valuationOf q) (1690)) (countLit q [-2, -4, -5, -6, -10, -11, -12, -15, -18, -21, -22, -23, -25, -27, -30, -31, -35, -37, -38, -39, -43, -45, -49, -50, -53, -55, -57, -58, -60]) (countLit q [-62, -63, -66, -69, -71, -72, -74, -75, -79, -80, -81, -82, -86, -89, -90, -92, -93, -95, -98, -99, -100, -101, -105, -107, -108, -112, -113, -114, -115]) (count1673 q) 7 11 (meaning1530 q) (meaning1665 q) (meaning1690 q) hs
  change valuationOf q 1530 = false ∨ valuationOf q 1665 = false ∨ valuationOf q 1690 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1306 (q : Snake 81) (h : Conditions q) : valuation q 1530 = false ∨ valuation q 1665 = false ∨ valuation q 1690 = true := counterClause1306 (baseVal q)

theorem counterClause1307 (q : Nat → Bool) : valuationOf q 1531 = false ∨ valuationOf q 1664 = false ∨ valuationOf q 1690 = true := by
  have hs : count1673 q = (countLit q [-2, -4, -5, -6, -10, -11, -12, -15, -18, -21, -22, -23, -25, -27, -30, -31, -35, -37, -38, -39, -43, -45, -49, -50, -53, -55, -57, -58, -60]) + (countLit q [-62, -63, -66, -69, -71, -72, -74, -75, -79, -80, -81, -82, -86, -89, -90, -92, -93, -95, -98, -99, -100, -101, -105, -107, -108, -112, -113, -114, -115]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5, -6, -10, -11, -12, -15, -18, -21, -22, -23, -25, -27, -30, -31, -35, -37, -38, -39, -43, -45, -49, -50, -53, -55, -57, -58, -60]) (l₂ := [-62, -63, -66, -69, -71, -72, -74, -75, -79, -80, -81, -82, -86, -89, -90, -92, -93, -95, -98, -99, -100, -101, -105, -107, -108, -112, -113, -114, -115])
  have hm := merge_two (literal (valuationOf q) (1531)) (literal (valuationOf q) (1664)) (literal (valuationOf q) (1690)) (countLit q [-2, -4, -5, -6, -10, -11, -12, -15, -18, -21, -22, -23, -25, -27, -30, -31, -35, -37, -38, -39, -43, -45, -49, -50, -53, -55, -57, -58, -60]) (countLit q [-62, -63, -66, -69, -71, -72, -74, -75, -79, -80, -81, -82, -86, -89, -90, -92, -93, -95, -98, -99, -100, -101, -105, -107, -108, -112, -113, -114, -115]) (count1673 q) 8 10 (meaning1531 q) (meaning1664 q) (meaning1690 q) hs
  change valuationOf q 1531 = false ∨ valuationOf q 1664 = false ∨ valuationOf q 1690 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1307 (q : Snake 81) (h : Conditions q) : valuation q 1531 = false ∨ valuation q 1664 = false ∨ valuation q 1690 = true := counterClause1307 (baseVal q)

theorem counterClause1308 (q : Nat → Bool) : valuationOf q 1532 = false ∨ valuationOf q 1663 = false ∨ valuationOf q 1690 = true := by
  have hs : count1673 q = (countLit q [-2, -4, -5, -6, -10, -11, -12, -15, -18, -21, -22, -23, -25, -27, -30, -31, -35, -37, -38, -39, -43, -45, -49, -50, -53, -55, -57, -58, -60]) + (countLit q [-62, -63, -66, -69, -71, -72, -74, -75, -79, -80, -81, -82, -86, -89, -90, -92, -93, -95, -98, -99, -100, -101, -105, -107, -108, -112, -113, -114, -115]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5, -6, -10, -11, -12, -15, -18, -21, -22, -23, -25, -27, -30, -31, -35, -37, -38, -39, -43, -45, -49, -50, -53, -55, -57, -58, -60]) (l₂ := [-62, -63, -66, -69, -71, -72, -74, -75, -79, -80, -81, -82, -86, -89, -90, -92, -93, -95, -98, -99, -100, -101, -105, -107, -108, -112, -113, -114, -115])
  have hm := merge_two (literal (valuationOf q) (1532)) (literal (valuationOf q) (1663)) (literal (valuationOf q) (1690)) (countLit q [-2, -4, -5, -6, -10, -11, -12, -15, -18, -21, -22, -23, -25, -27, -30, -31, -35, -37, -38, -39, -43, -45, -49, -50, -53, -55, -57, -58, -60]) (countLit q [-62, -63, -66, -69, -71, -72, -74, -75, -79, -80, -81, -82, -86, -89, -90, -92, -93, -95, -98, -99, -100, -101, -105, -107, -108, -112, -113, -114, -115]) (count1673 q) 9 9 (meaning1532 q) (meaning1663 q) (meaning1690 q) hs
  change valuationOf q 1532 = false ∨ valuationOf q 1663 = false ∨ valuationOf q 1690 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1308 (q : Snake 81) (h : Conditions q) : valuation q 1532 = false ∨ valuation q 1663 = false ∨ valuation q 1690 = true := counterClause1308 (baseVal q)

theorem counterClause1309 (q : Nat → Bool) : valuationOf q 1533 = false ∨ valuationOf q 1662 = false ∨ valuationOf q 1690 = true := by
  have hs : count1673 q = (countLit q [-2, -4, -5, -6, -10, -11, -12, -15, -18, -21, -22, -23, -25, -27, -30, -31, -35, -37, -38, -39, -43, -45, -49, -50, -53, -55, -57, -58, -60]) + (countLit q [-62, -63, -66, -69, -71, -72, -74, -75, -79, -80, -81, -82, -86, -89, -90, -92, -93, -95, -98, -99, -100, -101, -105, -107, -108, -112, -113, -114, -115]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5, -6, -10, -11, -12, -15, -18, -21, -22, -23, -25, -27, -30, -31, -35, -37, -38, -39, -43, -45, -49, -50, -53, -55, -57, -58, -60]) (l₂ := [-62, -63, -66, -69, -71, -72, -74, -75, -79, -80, -81, -82, -86, -89, -90, -92, -93, -95, -98, -99, -100, -101, -105, -107, -108, -112, -113, -114, -115])
  have hm := merge_two (literal (valuationOf q) (1533)) (literal (valuationOf q) (1662)) (literal (valuationOf q) (1690)) (countLit q [-2, -4, -5, -6, -10, -11, -12, -15, -18, -21, -22, -23, -25, -27, -30, -31, -35, -37, -38, -39, -43, -45, -49, -50, -53, -55, -57, -58, -60]) (countLit q [-62, -63, -66, -69, -71, -72, -74, -75, -79, -80, -81, -82, -86, -89, -90, -92, -93, -95, -98, -99, -100, -101, -105, -107, -108, -112, -113, -114, -115]) (count1673 q) 10 8 (meaning1533 q) (meaning1662 q) (meaning1690 q) hs
  change valuationOf q 1533 = false ∨ valuationOf q 1662 = false ∨ valuationOf q 1690 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1309 (q : Snake 81) (h : Conditions q) : valuation q 1533 = false ∨ valuation q 1662 = false ∨ valuation q 1690 = true := counterClause1309 (baseVal q)

theorem counterClause1310 (q : Nat → Bool) : valuationOf q 1534 = false ∨ valuationOf q 1661 = false ∨ valuationOf q 1690 = true := by
  have hs : count1673 q = (countLit q [-2, -4, -5, -6, -10, -11, -12, -15, -18, -21, -22, -23, -25, -27, -30, -31, -35, -37, -38, -39, -43, -45, -49, -50, -53, -55, -57, -58, -60]) + (countLit q [-62, -63, -66, -69, -71, -72, -74, -75, -79, -80, -81, -82, -86, -89, -90, -92, -93, -95, -98, -99, -100, -101, -105, -107, -108, -112, -113, -114, -115]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5, -6, -10, -11, -12, -15, -18, -21, -22, -23, -25, -27, -30, -31, -35, -37, -38, -39, -43, -45, -49, -50, -53, -55, -57, -58, -60]) (l₂ := [-62, -63, -66, -69, -71, -72, -74, -75, -79, -80, -81, -82, -86, -89, -90, -92, -93, -95, -98, -99, -100, -101, -105, -107, -108, -112, -113, -114, -115])
  have hm := merge_two (literal (valuationOf q) (1534)) (literal (valuationOf q) (1661)) (literal (valuationOf q) (1690)) (countLit q [-2, -4, -5, -6, -10, -11, -12, -15, -18, -21, -22, -23, -25, -27, -30, -31, -35, -37, -38, -39, -43, -45, -49, -50, -53, -55, -57, -58, -60]) (countLit q [-62, -63, -66, -69, -71, -72, -74, -75, -79, -80, -81, -82, -86, -89, -90, -92, -93, -95, -98, -99, -100, -101, -105, -107, -108, -112, -113, -114, -115]) (count1673 q) 11 7 (meaning1534 q) (meaning1661 q) (meaning1690 q) hs
  change valuationOf q 1534 = false ∨ valuationOf q 1661 = false ∨ valuationOf q 1690 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1310 (q : Snake 81) (h : Conditions q) : valuation q 1534 = false ∨ valuation q 1661 = false ∨ valuation q 1690 = true := counterClause1310 (baseVal q)

theorem counterClause1311 (q : Nat → Bool) : valuationOf q 1535 = false ∨ valuationOf q 1660 = false ∨ valuationOf q 1690 = true := by
  have hs : count1673 q = (countLit q [-2, -4, -5, -6, -10, -11, -12, -15, -18, -21, -22, -23, -25, -27, -30, -31, -35, -37, -38, -39, -43, -45, -49, -50, -53, -55, -57, -58, -60]) + (countLit q [-62, -63, -66, -69, -71, -72, -74, -75, -79, -80, -81, -82, -86, -89, -90, -92, -93, -95, -98, -99, -100, -101, -105, -107, -108, -112, -113, -114, -115]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5, -6, -10, -11, -12, -15, -18, -21, -22, -23, -25, -27, -30, -31, -35, -37, -38, -39, -43, -45, -49, -50, -53, -55, -57, -58, -60]) (l₂ := [-62, -63, -66, -69, -71, -72, -74, -75, -79, -80, -81, -82, -86, -89, -90, -92, -93, -95, -98, -99, -100, -101, -105, -107, -108, -112, -113, -114, -115])
  have hm := merge_two (literal (valuationOf q) (1535)) (literal (valuationOf q) (1660)) (literal (valuationOf q) (1690)) (countLit q [-2, -4, -5, -6, -10, -11, -12, -15, -18, -21, -22, -23, -25, -27, -30, -31, -35, -37, -38, -39, -43, -45, -49, -50, -53, -55, -57, -58, -60]) (countLit q [-62, -63, -66, -69, -71, -72, -74, -75, -79, -80, -81, -82, -86, -89, -90, -92, -93, -95, -98, -99, -100, -101, -105, -107, -108, -112, -113, -114, -115]) (count1673 q) 12 6 (meaning1535 q) (meaning1660 q) (meaning1690 q) hs
  change valuationOf q 1535 = false ∨ valuationOf q 1660 = false ∨ valuationOf q 1690 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1311 (q : Snake 81) (h : Conditions q) : valuation q 1535 = false ∨ valuation q 1660 = false ∨ valuation q 1690 = true := counterClause1311 (baseVal q)

theorem counterClause1312 (q : Nat → Bool) : valuationOf q 1536 = false ∨ valuationOf q 1659 = false ∨ valuationOf q 1690 = true := by
  have hs : count1673 q = (countLit q [-2, -4, -5, -6, -10, -11, -12, -15, -18, -21, -22, -23, -25, -27, -30, -31, -35, -37, -38, -39, -43, -45, -49, -50, -53, -55, -57, -58, -60]) + (countLit q [-62, -63, -66, -69, -71, -72, -74, -75, -79, -80, -81, -82, -86, -89, -90, -92, -93, -95, -98, -99, -100, -101, -105, -107, -108, -112, -113, -114, -115]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5, -6, -10, -11, -12, -15, -18, -21, -22, -23, -25, -27, -30, -31, -35, -37, -38, -39, -43, -45, -49, -50, -53, -55, -57, -58, -60]) (l₂ := [-62, -63, -66, -69, -71, -72, -74, -75, -79, -80, -81, -82, -86, -89, -90, -92, -93, -95, -98, -99, -100, -101, -105, -107, -108, -112, -113, -114, -115])
  have hm := merge_two (literal (valuationOf q) (1536)) (literal (valuationOf q) (1659)) (literal (valuationOf q) (1690)) (countLit q [-2, -4, -5, -6, -10, -11, -12, -15, -18, -21, -22, -23, -25, -27, -30, -31, -35, -37, -38, -39, -43, -45, -49, -50, -53, -55, -57, -58, -60]) (countLit q [-62, -63, -66, -69, -71, -72, -74, -75, -79, -80, -81, -82, -86, -89, -90, -92, -93, -95, -98, -99, -100, -101, -105, -107, -108, -112, -113, -114, -115]) (count1673 q) 13 5 (meaning1536 q) (meaning1659 q) (meaning1690 q) hs
  change valuationOf q 1536 = false ∨ valuationOf q 1659 = false ∨ valuationOf q 1690 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1312 (q : Snake 81) (h : Conditions q) : valuation q 1536 = false ∨ valuation q 1659 = false ∨ valuation q 1690 = true := counterClause1312 (baseVal q)

theorem block40 (q : Snake 81) (h : Conditions q) : B112E207.Block40 (valuation q) :=
  ⟨clause1281 q h, clause1282 q h, clause1283 q h, clause1284 q h, clause1285 q h, clause1286 q h, clause1287 q h, clause1288 q h, clause1289 q h, clause1290 q h, clause1291 q h, clause1292 q h, clause1293 q h, clause1294 q h, clause1295 q h, clause1296 q h, clause1297 q h, clause1298 q h, clause1299 q h, clause1300 q h, clause1301 q h, clause1302 q h, clause1303 q h, clause1304 q h, clause1305 q h, clause1306 q h, clause1307 q h, clause1308 q h, clause1309 q h, clause1310 q h, clause1311 q h, clause1312 q h⟩

end
end Snake9.Regrowth.E112207
