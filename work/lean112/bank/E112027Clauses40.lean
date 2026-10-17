import E112027Semantics
import B112E027Inputs
namespace Snake9.Regrowth.E112027
noncomputable section
local instance blockDec40 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1281 (q : Nat → Bool) : valuationOf q 1618 = false ∨ valuationOf q 1625 = false ∨ valuationOf q 1630 = true := by
  have hs : count1629 q = (countLit q [-90, -92, -95]) + (countLit q [-96, -97, -98, -102]) := List.countP_append (p := literal q) (l₁ := [-90, -92, -95]) (l₂ := [-96, -97, -98, -102])
  have hm := merge_two (literal (valuationOf q) (1618)) (literal (valuationOf q) (1625)) (literal (valuationOf q) (1630)) (countLit q [-90, -92, -95]) (countLit q [-96, -97, -98, -102]) (count1629 q) 1 1 (meaning1618 q) (meaning1625 q) (meaning1630 q) hs
  change valuationOf q 1618 = false ∨ valuationOf q 1625 = false ∨ valuationOf q 1630 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1281 (q : Snake 81) (h : Conditions q) : valuation q 1618 = false ∨ valuation q 1625 = false ∨ valuation q 1630 = true := counterClause1281 (baseVal q)

theorem counterClause1282 (q : Nat → Bool) : valuationOf q 1618 = false ∨ valuationOf q 1626 = false ∨ valuationOf q 1631 = true := by
  have hs : count1629 q = (countLit q [-90, -92, -95]) + (countLit q [-96, -97, -98, -102]) := List.countP_append (p := literal q) (l₁ := [-90, -92, -95]) (l₂ := [-96, -97, -98, -102])
  have hm := merge_two (literal (valuationOf q) (1618)) (literal (valuationOf q) (1626)) (literal (valuationOf q) (1631)) (countLit q [-90, -92, -95]) (countLit q [-96, -97, -98, -102]) (count1629 q) 1 2 (meaning1618 q) (meaning1626 q) (meaning1631 q) hs
  change valuationOf q 1618 = false ∨ valuationOf q 1626 = false ∨ valuationOf q 1631 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1282 (q : Snake 81) (h : Conditions q) : valuation q 1618 = false ∨ valuation q 1626 = false ∨ valuation q 1631 = true := counterClause1282 (baseVal q)

theorem counterClause1283 (q : Nat → Bool) : valuationOf q 1618 = false ∨ valuationOf q 1627 = false ∨ valuationOf q 1632 = true := by
  have hs : count1629 q = (countLit q [-90, -92, -95]) + (countLit q [-96, -97, -98, -102]) := List.countP_append (p := literal q) (l₁ := [-90, -92, -95]) (l₂ := [-96, -97, -98, -102])
  have hm := merge_two (literal (valuationOf q) (1618)) (literal (valuationOf q) (1627)) (literal (valuationOf q) (1632)) (countLit q [-90, -92, -95]) (countLit q [-96, -97, -98, -102]) (count1629 q) 1 3 (meaning1618 q) (meaning1627 q) (meaning1632 q) hs
  change valuationOf q 1618 = false ∨ valuationOf q 1627 = false ∨ valuationOf q 1632 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1283 (q : Snake 81) (h : Conditions q) : valuation q 1618 = false ∨ valuation q 1627 = false ∨ valuation q 1632 = true := counterClause1283 (baseVal q)

theorem counterClause1284 (q : Nat → Bool) : valuationOf q 1618 = false ∨ valuationOf q 1628 = false ∨ valuationOf q 1633 = true := by
  have hs : count1629 q = (countLit q [-90, -92, -95]) + (countLit q [-96, -97, -98, -102]) := List.countP_append (p := literal q) (l₁ := [-90, -92, -95]) (l₂ := [-96, -97, -98, -102])
  have hm := merge_two (literal (valuationOf q) (1618)) (literal (valuationOf q) (1628)) (literal (valuationOf q) (1633)) (countLit q [-90, -92, -95]) (countLit q [-96, -97, -98, -102]) (count1629 q) 1 4 (meaning1618 q) (meaning1628 q) (meaning1633 q) hs
  change valuationOf q 1618 = false ∨ valuationOf q 1628 = false ∨ valuationOf q 1633 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1284 (q : Snake 81) (h : Conditions q) : valuation q 1618 = false ∨ valuation q 1628 = false ∨ valuation q 1633 = true := counterClause1284 (baseVal q)

theorem counterClause1285 (q : Nat → Bool) : valuationOf q 1619 = false ∨ valuationOf q 1630 = true := by
  have hs : count1629 q = (countLit q [-90, -92, -95]) + (countLit q [-96, -97, -98, -102]) := List.countP_append (p := literal q) (l₁ := [-90, -92, -95]) (l₂ := [-96, -97, -98, -102])
  have hm := merge_left (literal (valuationOf q) (1619)) (literal (valuationOf q) (1630)) (countLit q [-90, -92, -95]) (countLit q [-96, -97, -98, -102]) (count1629 q) 2 (meaning1619 q) (meaning1630 q) hs
  change valuationOf q 1619 = false ∨ valuationOf q 1630 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1285 (q : Snake 81) (h : Conditions q) : valuation q 1619 = false ∨ valuation q 1630 = true := counterClause1285 (baseVal q)

theorem counterClause1286 (q : Nat → Bool) : valuationOf q 1619 = false ∨ valuationOf q 1625 = false ∨ valuationOf q 1631 = true := by
  have hs : count1629 q = (countLit q [-90, -92, -95]) + (countLit q [-96, -97, -98, -102]) := List.countP_append (p := literal q) (l₁ := [-90, -92, -95]) (l₂ := [-96, -97, -98, -102])
  have hm := merge_two (literal (valuationOf q) (1619)) (literal (valuationOf q) (1625)) (literal (valuationOf q) (1631)) (countLit q [-90, -92, -95]) (countLit q [-96, -97, -98, -102]) (count1629 q) 2 1 (meaning1619 q) (meaning1625 q) (meaning1631 q) hs
  change valuationOf q 1619 = false ∨ valuationOf q 1625 = false ∨ valuationOf q 1631 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1286 (q : Snake 81) (h : Conditions q) : valuation q 1619 = false ∨ valuation q 1625 = false ∨ valuation q 1631 = true := counterClause1286 (baseVal q)

theorem counterClause1287 (q : Nat → Bool) : valuationOf q 1619 = false ∨ valuationOf q 1626 = false ∨ valuationOf q 1632 = true := by
  have hs : count1629 q = (countLit q [-90, -92, -95]) + (countLit q [-96, -97, -98, -102]) := List.countP_append (p := literal q) (l₁ := [-90, -92, -95]) (l₂ := [-96, -97, -98, -102])
  have hm := merge_two (literal (valuationOf q) (1619)) (literal (valuationOf q) (1626)) (literal (valuationOf q) (1632)) (countLit q [-90, -92, -95]) (countLit q [-96, -97, -98, -102]) (count1629 q) 2 2 (meaning1619 q) (meaning1626 q) (meaning1632 q) hs
  change valuationOf q 1619 = false ∨ valuationOf q 1626 = false ∨ valuationOf q 1632 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1287 (q : Snake 81) (h : Conditions q) : valuation q 1619 = false ∨ valuation q 1626 = false ∨ valuation q 1632 = true := counterClause1287 (baseVal q)

theorem counterClause1288 (q : Nat → Bool) : valuationOf q 1619 = false ∨ valuationOf q 1627 = false ∨ valuationOf q 1633 = true := by
  have hs : count1629 q = (countLit q [-90, -92, -95]) + (countLit q [-96, -97, -98, -102]) := List.countP_append (p := literal q) (l₁ := [-90, -92, -95]) (l₂ := [-96, -97, -98, -102])
  have hm := merge_two (literal (valuationOf q) (1619)) (literal (valuationOf q) (1627)) (literal (valuationOf q) (1633)) (countLit q [-90, -92, -95]) (countLit q [-96, -97, -98, -102]) (count1629 q) 2 3 (meaning1619 q) (meaning1627 q) (meaning1633 q) hs
  change valuationOf q 1619 = false ∨ valuationOf q 1627 = false ∨ valuationOf q 1633 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1288 (q : Snake 81) (h : Conditions q) : valuation q 1619 = false ∨ valuation q 1627 = false ∨ valuation q 1633 = true := counterClause1288 (baseVal q)

theorem counterClause1289 (q : Nat → Bool) : valuationOf q 1619 = false ∨ valuationOf q 1628 = false ∨ valuationOf q 1634 = true := by
  have hs : count1629 q = (countLit q [-90, -92, -95]) + (countLit q [-96, -97, -98, -102]) := List.countP_append (p := literal q) (l₁ := [-90, -92, -95]) (l₂ := [-96, -97, -98, -102])
  have hm := merge_two (literal (valuationOf q) (1619)) (literal (valuationOf q) (1628)) (literal (valuationOf q) (1634)) (countLit q [-90, -92, -95]) (countLit q [-96, -97, -98, -102]) (count1629 q) 2 4 (meaning1619 q) (meaning1628 q) (meaning1634 q) hs
  change valuationOf q 1619 = false ∨ valuationOf q 1628 = false ∨ valuationOf q 1634 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1289 (q : Snake 81) (h : Conditions q) : valuation q 1619 = false ∨ valuation q 1628 = false ∨ valuation q 1634 = true := counterClause1289 (baseVal q)

theorem counterClause1290 (q : Nat → Bool) : valuationOf q 1620 = false ∨ valuationOf q 1631 = true := by
  have hs : count1629 q = (countLit q [-90, -92, -95]) + (countLit q [-96, -97, -98, -102]) := List.countP_append (p := literal q) (l₁ := [-90, -92, -95]) (l₂ := [-96, -97, -98, -102])
  have hm := merge_left (literal (valuationOf q) (1620)) (literal (valuationOf q) (1631)) (countLit q [-90, -92, -95]) (countLit q [-96, -97, -98, -102]) (count1629 q) 3 (meaning1620 q) (meaning1631 q) hs
  change valuationOf q 1620 = false ∨ valuationOf q 1631 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1290 (q : Snake 81) (h : Conditions q) : valuation q 1620 = false ∨ valuation q 1631 = true := counterClause1290 (baseVal q)

theorem counterClause1291 (q : Nat → Bool) : valuationOf q 1620 = false ∨ valuationOf q 1625 = false ∨ valuationOf q 1632 = true := by
  have hs : count1629 q = (countLit q [-90, -92, -95]) + (countLit q [-96, -97, -98, -102]) := List.countP_append (p := literal q) (l₁ := [-90, -92, -95]) (l₂ := [-96, -97, -98, -102])
  have hm := merge_two (literal (valuationOf q) (1620)) (literal (valuationOf q) (1625)) (literal (valuationOf q) (1632)) (countLit q [-90, -92, -95]) (countLit q [-96, -97, -98, -102]) (count1629 q) 3 1 (meaning1620 q) (meaning1625 q) (meaning1632 q) hs
  change valuationOf q 1620 = false ∨ valuationOf q 1625 = false ∨ valuationOf q 1632 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1291 (q : Snake 81) (h : Conditions q) : valuation q 1620 = false ∨ valuation q 1625 = false ∨ valuation q 1632 = true := counterClause1291 (baseVal q)

theorem counterClause1292 (q : Nat → Bool) : valuationOf q 1620 = false ∨ valuationOf q 1626 = false ∨ valuationOf q 1633 = true := by
  have hs : count1629 q = (countLit q [-90, -92, -95]) + (countLit q [-96, -97, -98, -102]) := List.countP_append (p := literal q) (l₁ := [-90, -92, -95]) (l₂ := [-96, -97, -98, -102])
  have hm := merge_two (literal (valuationOf q) (1620)) (literal (valuationOf q) (1626)) (literal (valuationOf q) (1633)) (countLit q [-90, -92, -95]) (countLit q [-96, -97, -98, -102]) (count1629 q) 3 2 (meaning1620 q) (meaning1626 q) (meaning1633 q) hs
  change valuationOf q 1620 = false ∨ valuationOf q 1626 = false ∨ valuationOf q 1633 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1292 (q : Snake 81) (h : Conditions q) : valuation q 1620 = false ∨ valuation q 1626 = false ∨ valuation q 1633 = true := counterClause1292 (baseVal q)

theorem counterClause1293 (q : Nat → Bool) : valuationOf q 1620 = false ∨ valuationOf q 1627 = false ∨ valuationOf q 1634 = true := by
  have hs : count1629 q = (countLit q [-90, -92, -95]) + (countLit q [-96, -97, -98, -102]) := List.countP_append (p := literal q) (l₁ := [-90, -92, -95]) (l₂ := [-96, -97, -98, -102])
  have hm := merge_two (literal (valuationOf q) (1620)) (literal (valuationOf q) (1627)) (literal (valuationOf q) (1634)) (countLit q [-90, -92, -95]) (countLit q [-96, -97, -98, -102]) (count1629 q) 3 3 (meaning1620 q) (meaning1627 q) (meaning1634 q) hs
  change valuationOf q 1620 = false ∨ valuationOf q 1627 = false ∨ valuationOf q 1634 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1293 (q : Snake 81) (h : Conditions q) : valuation q 1620 = false ∨ valuation q 1627 = false ∨ valuation q 1634 = true := counterClause1293 (baseVal q)

theorem counterClause1294 (q : Nat → Bool) : valuationOf q 105 = true ∨ valuationOf q 1636 = true := by
  have hs : count1636 q = (countLit q [-104]) + (countLit q [-105]) := List.countP_append (p := literal q) (l₁ := [-104]) (l₂ := [-105])
  have hm := merge_right (literal (valuationOf q) (-105)) (literal (valuationOf q) (1636)) (countLit q [-104]) (countLit q [-105]) (count1636 q) 1 (meaningNeg105 q) (meaning1636 q) hs
  change (! (valuationOf q 105)) = false ∨ valuationOf q 1636 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1294 (q : Snake 81) (h : Conditions q) : valuation q 105 = true ∨ valuation q 1636 = true := counterClause1294 (baseVal q)

theorem counterClause1295 (q : Nat → Bool) : valuationOf q 104 = true ∨ valuationOf q 1636 = true := by
  have hs : count1636 q = (countLit q [-104]) + (countLit q [-105]) := List.countP_append (p := literal q) (l₁ := [-104]) (l₂ := [-105])
  have hm := merge_left (literal (valuationOf q) (-104)) (literal (valuationOf q) (1636)) (countLit q [-104]) (countLit q [-105]) (count1636 q) 1 (meaningNeg104 q) (meaning1636 q) hs
  change (! (valuationOf q 104)) = false ∨ valuationOf q 1636 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1295 (q : Snake 81) (h : Conditions q) : valuation q 104 = true ∨ valuation q 1636 = true := counterClause1295 (baseVal q)

theorem counterClause1296 (q : Nat → Bool) : valuationOf q 104 = true ∨ valuationOf q 105 = true ∨ valuationOf q 1637 = true := by
  have hs : count1636 q = (countLit q [-104]) + (countLit q [-105]) := List.countP_append (p := literal q) (l₁ := [-104]) (l₂ := [-105])
  have hm := merge_two (literal (valuationOf q) (-104)) (literal (valuationOf q) (-105)) (literal (valuationOf q) (1637)) (countLit q [-104]) (countLit q [-105]) (count1636 q) 1 1 (meaningNeg104 q) (meaningNeg105 q) (meaning1637 q) hs
  change (! (valuationOf q 104)) = false ∨ (! (valuationOf q 105)) = false ∨ valuationOf q 1637 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1296 (q : Snake 81) (h : Conditions q) : valuation q 104 = true ∨ valuation q 105 = true ∨ valuation q 1637 = true := counterClause1296 (baseVal q)

theorem counterClause1297 (q : Nat → Bool) : valuationOf q 108 = true ∨ valuationOf q 1638 = true := by
  have hs : count1638 q = (countLit q [-106]) + (countLit q [-108]) := List.countP_append (p := literal q) (l₁ := [-106]) (l₂ := [-108])
  have hm := merge_right (literal (valuationOf q) (-108)) (literal (valuationOf q) (1638)) (countLit q [-106]) (countLit q [-108]) (count1638 q) 1 (meaningNeg108 q) (meaning1638 q) hs
  change (! (valuationOf q 108)) = false ∨ valuationOf q 1638 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1297 (q : Snake 81) (h : Conditions q) : valuation q 108 = true ∨ valuation q 1638 = true := counterClause1297 (baseVal q)

theorem counterClause1298 (q : Nat → Bool) : valuationOf q 106 = true ∨ valuationOf q 1638 = true := by
  have hs : count1638 q = (countLit q [-106]) + (countLit q [-108]) := List.countP_append (p := literal q) (l₁ := [-106]) (l₂ := [-108])
  have hm := merge_left (literal (valuationOf q) (-106)) (literal (valuationOf q) (1638)) (countLit q [-106]) (countLit q [-108]) (count1638 q) 1 (meaningNeg106 q) (meaning1638 q) hs
  change (! (valuationOf q 106)) = false ∨ valuationOf q 1638 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1298 (q : Snake 81) (h : Conditions q) : valuation q 106 = true ∨ valuation q 1638 = true := counterClause1298 (baseVal q)

theorem counterClause1299 (q : Nat → Bool) : valuationOf q 106 = true ∨ valuationOf q 108 = true ∨ valuationOf q 1639 = true := by
  have hs : count1638 q = (countLit q [-106]) + (countLit q [-108]) := List.countP_append (p := literal q) (l₁ := [-106]) (l₂ := [-108])
  have hm := merge_two (literal (valuationOf q) (-106)) (literal (valuationOf q) (-108)) (literal (valuationOf q) (1639)) (countLit q [-106]) (countLit q [-108]) (count1638 q) 1 1 (meaningNeg106 q) (meaningNeg108 q) (meaning1639 q) hs
  change (! (valuationOf q 106)) = false ∨ (! (valuationOf q 108)) = false ∨ valuationOf q 1639 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1299 (q : Snake 81) (h : Conditions q) : valuation q 106 = true ∨ valuation q 108 = true ∨ valuation q 1639 = true := counterClause1299 (baseVal q)

theorem counterClause1300 (q : Nat → Bool) : valuationOf q 1638 = false ∨ valuationOf q 1640 = true := by
  have hs : count1640 q = (countLit q [-104, -105]) + (countLit q [-106, -108]) := List.countP_append (p := literal q) (l₁ := [-104, -105]) (l₂ := [-106, -108])
  have hm := merge_right (literal (valuationOf q) (1638)) (literal (valuationOf q) (1640)) (countLit q [-104, -105]) (countLit q [-106, -108]) (count1640 q) 1 (meaning1638 q) (meaning1640 q) hs
  change valuationOf q 1638 = false ∨ valuationOf q 1640 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1300 (q : Snake 81) (h : Conditions q) : valuation q 1638 = false ∨ valuation q 1640 = true := counterClause1300 (baseVal q)

theorem counterClause1301 (q : Nat → Bool) : valuationOf q 1639 = false ∨ valuationOf q 1641 = true := by
  have hs : count1640 q = (countLit q [-104, -105]) + (countLit q [-106, -108]) := List.countP_append (p := literal q) (l₁ := [-104, -105]) (l₂ := [-106, -108])
  have hm := merge_right (literal (valuationOf q) (1639)) (literal (valuationOf q) (1641)) (countLit q [-104, -105]) (countLit q [-106, -108]) (count1640 q) 2 (meaning1639 q) (meaning1641 q) hs
  change valuationOf q 1639 = false ∨ valuationOf q 1641 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1301 (q : Snake 81) (h : Conditions q) : valuation q 1639 = false ∨ valuation q 1641 = true := counterClause1301 (baseVal q)

theorem counterClause1302 (q : Nat → Bool) : valuationOf q 1636 = false ∨ valuationOf q 1640 = true := by
  have hs : count1640 q = (countLit q [-104, -105]) + (countLit q [-106, -108]) := List.countP_append (p := literal q) (l₁ := [-104, -105]) (l₂ := [-106, -108])
  have hm := merge_left (literal (valuationOf q) (1636)) (literal (valuationOf q) (1640)) (countLit q [-104, -105]) (countLit q [-106, -108]) (count1640 q) 1 (meaning1636 q) (meaning1640 q) hs
  change valuationOf q 1636 = false ∨ valuationOf q 1640 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1302 (q : Snake 81) (h : Conditions q) : valuation q 1636 = false ∨ valuation q 1640 = true := counterClause1302 (baseVal q)

theorem counterClause1303 (q : Nat → Bool) : valuationOf q 1636 = false ∨ valuationOf q 1638 = false ∨ valuationOf q 1641 = true := by
  have hs : count1640 q = (countLit q [-104, -105]) + (countLit q [-106, -108]) := List.countP_append (p := literal q) (l₁ := [-104, -105]) (l₂ := [-106, -108])
  have hm := merge_two (literal (valuationOf q) (1636)) (literal (valuationOf q) (1638)) (literal (valuationOf q) (1641)) (countLit q [-104, -105]) (countLit q [-106, -108]) (count1640 q) 1 1 (meaning1636 q) (meaning1638 q) (meaning1641 q) hs
  change valuationOf q 1636 = false ∨ valuationOf q 1638 = false ∨ valuationOf q 1641 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1303 (q : Snake 81) (h : Conditions q) : valuation q 1636 = false ∨ valuation q 1638 = false ∨ valuation q 1641 = true := counterClause1303 (baseVal q)

theorem counterClause1304 (q : Nat → Bool) : valuationOf q 1636 = false ∨ valuationOf q 1639 = false ∨ valuationOf q 1642 = true := by
  have hs : count1640 q = (countLit q [-104, -105]) + (countLit q [-106, -108]) := List.countP_append (p := literal q) (l₁ := [-104, -105]) (l₂ := [-106, -108])
  have hm := merge_two (literal (valuationOf q) (1636)) (literal (valuationOf q) (1639)) (literal (valuationOf q) (1642)) (countLit q [-104, -105]) (countLit q [-106, -108]) (count1640 q) 1 2 (meaning1636 q) (meaning1639 q) (meaning1642 q) hs
  change valuationOf q 1636 = false ∨ valuationOf q 1639 = false ∨ valuationOf q 1642 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1304 (q : Snake 81) (h : Conditions q) : valuation q 1636 = false ∨ valuation q 1639 = false ∨ valuation q 1642 = true := counterClause1304 (baseVal q)

theorem counterClause1305 (q : Nat → Bool) : valuationOf q 1637 = false ∨ valuationOf q 1641 = true := by
  have hs : count1640 q = (countLit q [-104, -105]) + (countLit q [-106, -108]) := List.countP_append (p := literal q) (l₁ := [-104, -105]) (l₂ := [-106, -108])
  have hm := merge_left (literal (valuationOf q) (1637)) (literal (valuationOf q) (1641)) (countLit q [-104, -105]) (countLit q [-106, -108]) (count1640 q) 2 (meaning1637 q) (meaning1641 q) hs
  change valuationOf q 1637 = false ∨ valuationOf q 1641 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1305 (q : Snake 81) (h : Conditions q) : valuation q 1637 = false ∨ valuation q 1641 = true := counterClause1305 (baseVal q)

theorem counterClause1306 (q : Nat → Bool) : valuationOf q 1637 = false ∨ valuationOf q 1638 = false ∨ valuationOf q 1642 = true := by
  have hs : count1640 q = (countLit q [-104, -105]) + (countLit q [-106, -108]) := List.countP_append (p := literal q) (l₁ := [-104, -105]) (l₂ := [-106, -108])
  have hm := merge_two (literal (valuationOf q) (1637)) (literal (valuationOf q) (1638)) (literal (valuationOf q) (1642)) (countLit q [-104, -105]) (countLit q [-106, -108]) (count1640 q) 2 1 (meaning1637 q) (meaning1638 q) (meaning1642 q) hs
  change valuationOf q 1637 = false ∨ valuationOf q 1638 = false ∨ valuationOf q 1642 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1306 (q : Snake 81) (h : Conditions q) : valuation q 1637 = false ∨ valuation q 1638 = false ∨ valuation q 1642 = true := counterClause1306 (baseVal q)

theorem counterClause1307 (q : Nat → Bool) : valuationOf q 1637 = false ∨ valuationOf q 1639 = false ∨ valuationOf q 1643 = true := by
  have hs : count1640 q = (countLit q [-104, -105]) + (countLit q [-106, -108]) := List.countP_append (p := literal q) (l₁ := [-104, -105]) (l₂ := [-106, -108])
  have hm := merge_two (literal (valuationOf q) (1637)) (literal (valuationOf q) (1639)) (literal (valuationOf q) (1643)) (countLit q [-104, -105]) (countLit q [-106, -108]) (count1640 q) 2 2 (meaning1637 q) (meaning1639 q) (meaning1643 q) hs
  change valuationOf q 1637 = false ∨ valuationOf q 1639 = false ∨ valuationOf q 1643 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1307 (q : Snake 81) (h : Conditions q) : valuation q 1637 = false ∨ valuation q 1639 = false ∨ valuation q 1643 = true := counterClause1307 (baseVal q)

theorem counterClause1308 (q : Nat → Bool) : valuationOf q 114 = true ∨ valuationOf q 1644 = true := by
  have hs : count1644 q = (countLit q [-111]) + (countLit q [-114]) := List.countP_append (p := literal q) (l₁ := [-111]) (l₂ := [-114])
  have hm := merge_right (literal (valuationOf q) (-114)) (literal (valuationOf q) (1644)) (countLit q [-111]) (countLit q [-114]) (count1644 q) 1 (meaningNeg114 q) (meaning1644 q) hs
  change (! (valuationOf q 114)) = false ∨ valuationOf q 1644 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1308 (q : Snake 81) (h : Conditions q) : valuation q 114 = true ∨ valuation q 1644 = true := counterClause1308 (baseVal q)

theorem counterClause1309 (q : Nat → Bool) : valuationOf q 111 = true ∨ valuationOf q 1644 = true := by
  have hs : count1644 q = (countLit q [-111]) + (countLit q [-114]) := List.countP_append (p := literal q) (l₁ := [-111]) (l₂ := [-114])
  have hm := merge_left (literal (valuationOf q) (-111)) (literal (valuationOf q) (1644)) (countLit q [-111]) (countLit q [-114]) (count1644 q) 1 (meaningNeg111 q) (meaning1644 q) hs
  change (! (valuationOf q 111)) = false ∨ valuationOf q 1644 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1309 (q : Snake 81) (h : Conditions q) : valuation q 111 = true ∨ valuation q 1644 = true := counterClause1309 (baseVal q)

theorem counterClause1310 (q : Nat → Bool) : valuationOf q 111 = true ∨ valuationOf q 114 = true ∨ valuationOf q 1645 = true := by
  have hs : count1644 q = (countLit q [-111]) + (countLit q [-114]) := List.countP_append (p := literal q) (l₁ := [-111]) (l₂ := [-114])
  have hm := merge_two (literal (valuationOf q) (-111)) (literal (valuationOf q) (-114)) (literal (valuationOf q) (1645)) (countLit q [-111]) (countLit q [-114]) (count1644 q) 1 1 (meaningNeg111 q) (meaningNeg114 q) (meaning1645 q) hs
  change (! (valuationOf q 111)) = false ∨ (! (valuationOf q 114)) = false ∨ valuationOf q 1645 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1310 (q : Snake 81) (h : Conditions q) : valuation q 111 = true ∨ valuation q 114 = true ∨ valuation q 1645 = true := counterClause1310 (baseVal q)

theorem counterClause1311 (q : Nat → Bool) : valuationOf q 117 = true ∨ valuationOf q 1646 = true := by
  have hs : count1646 q = (countLit q [-115]) + (countLit q [-117]) := List.countP_append (p := literal q) (l₁ := [-115]) (l₂ := [-117])
  have hm := merge_right (literal (valuationOf q) (-117)) (literal (valuationOf q) (1646)) (countLit q [-115]) (countLit q [-117]) (count1646 q) 1 (meaningNeg117 q) (meaning1646 q) hs
  change (! (valuationOf q 117)) = false ∨ valuationOf q 1646 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1311 (q : Snake 81) (h : Conditions q) : valuation q 117 = true ∨ valuation q 1646 = true := counterClause1311 (baseVal q)

theorem counterClause1312 (q : Nat → Bool) : valuationOf q 115 = true ∨ valuationOf q 1646 = true := by
  have hs : count1646 q = (countLit q [-115]) + (countLit q [-117]) := List.countP_append (p := literal q) (l₁ := [-115]) (l₂ := [-117])
  have hm := merge_left (literal (valuationOf q) (-115)) (literal (valuationOf q) (1646)) (countLit q [-115]) (countLit q [-117]) (count1646 q) 1 (meaningNeg115 q) (meaning1646 q) hs
  change (! (valuationOf q 115)) = false ∨ valuationOf q 1646 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1312 (q : Snake 81) (h : Conditions q) : valuation q 115 = true ∨ valuation q 1646 = true := counterClause1312 (baseVal q)

theorem block40 (q : Snake 81) (h : Conditions q) : B112E027.Block40 (valuation q) :=
  ⟨clause1281 q h, clause1282 q h, clause1283 q h, clause1284 q h, clause1285 q h, clause1286 q h, clause1287 q h, clause1288 q h, clause1289 q h, clause1290 q h, clause1291 q h, clause1292 q h, clause1293 q h, clause1294 q h, clause1295 q h, clause1296 q h, clause1297 q h, clause1298 q h, clause1299 q h, clause1300 q h, clause1301 q h, clause1302 q h, clause1303 q h, clause1304 q h, clause1305 q h, clause1306 q h, clause1307 q h, clause1308 q h, clause1309 q h, clause1310 q h, clause1311 q h, clause1312 q h⟩

end
end Snake9.Regrowth.E112027
