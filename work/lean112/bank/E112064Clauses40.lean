import E112064Semantics
import B112E064Inputs
namespace Snake9.Regrowth.E112064
noncomputable section
local instance blockDec40 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1281 (q : Nat → Bool) : valuationOf q 110 = true ∨ valuationOf q 113 = true ∨ valuationOf q 1623 = true := by
  have hs : count1622 q = (countLit q [-110]) + (countLit q [-113]) := List.countP_append (p := literal q) (l₁ := [-110]) (l₂ := [-113])
  have hm := merge_two (literal (valuationOf q) (-110)) (literal (valuationOf q) (-113)) (literal (valuationOf q) (1623)) (countLit q [-110]) (countLit q [-113]) (count1622 q) 1 1 (meaningNeg110 q) (meaningNeg113 q) (meaning1623 q) hs
  change (! (valuationOf q 110)) = false ∨ (! (valuationOf q 113)) = false ∨ valuationOf q 1623 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1281 (q : Snake 81) (h : Conditions q) : valuation q 110 = true ∨ valuation q 113 = true ∨ valuation q 1623 = true := counterClause1281 (baseVal q)

theorem counterClause1282 (q : Nat → Bool) : valuationOf q 116 = true ∨ valuationOf q 1624 = true := by
  have hs : count1624 q = (countLit q [-114]) + (countLit q [-116]) := List.countP_append (p := literal q) (l₁ := [-114]) (l₂ := [-116])
  have hm := merge_right (literal (valuationOf q) (-116)) (literal (valuationOf q) (1624)) (countLit q [-114]) (countLit q [-116]) (count1624 q) 1 (meaningNeg116 q) (meaning1624 q) hs
  change (! (valuationOf q 116)) = false ∨ valuationOf q 1624 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1282 (q : Snake 81) (h : Conditions q) : valuation q 116 = true ∨ valuation q 1624 = true := counterClause1282 (baseVal q)

theorem counterClause1283 (q : Nat → Bool) : valuationOf q 114 = true ∨ valuationOf q 1624 = true := by
  have hs : count1624 q = (countLit q [-114]) + (countLit q [-116]) := List.countP_append (p := literal q) (l₁ := [-114]) (l₂ := [-116])
  have hm := merge_left (literal (valuationOf q) (-114)) (literal (valuationOf q) (1624)) (countLit q [-114]) (countLit q [-116]) (count1624 q) 1 (meaningNeg114 q) (meaning1624 q) hs
  change (! (valuationOf q 114)) = false ∨ valuationOf q 1624 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1283 (q : Snake 81) (h : Conditions q) : valuation q 114 = true ∨ valuation q 1624 = true := counterClause1283 (baseVal q)

theorem counterClause1284 (q : Nat → Bool) : valuationOf q 114 = true ∨ valuationOf q 116 = true ∨ valuationOf q 1625 = true := by
  have hs : count1624 q = (countLit q [-114]) + (countLit q [-116]) := List.countP_append (p := literal q) (l₁ := [-114]) (l₂ := [-116])
  have hm := merge_two (literal (valuationOf q) (-114)) (literal (valuationOf q) (-116)) (literal (valuationOf q) (1625)) (countLit q [-114]) (countLit q [-116]) (count1624 q) 1 1 (meaningNeg114 q) (meaningNeg116 q) (meaning1625 q) hs
  change (! (valuationOf q 114)) = false ∨ (! (valuationOf q 116)) = false ∨ valuationOf q 1625 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1284 (q : Snake 81) (h : Conditions q) : valuation q 114 = true ∨ valuation q 116 = true ∨ valuation q 1625 = true := counterClause1284 (baseVal q)

theorem counterClause1285 (q : Nat → Bool) : valuationOf q 1624 = false ∨ valuationOf q 1626 = true := by
  have hs : count1626 q = (countLit q [-110, -113]) + (countLit q [-114, -116]) := List.countP_append (p := literal q) (l₁ := [-110, -113]) (l₂ := [-114, -116])
  have hm := merge_right (literal (valuationOf q) (1624)) (literal (valuationOf q) (1626)) (countLit q [-110, -113]) (countLit q [-114, -116]) (count1626 q) 1 (meaning1624 q) (meaning1626 q) hs
  change valuationOf q 1624 = false ∨ valuationOf q 1626 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1285 (q : Snake 81) (h : Conditions q) : valuation q 1624 = false ∨ valuation q 1626 = true := counterClause1285 (baseVal q)

theorem counterClause1286 (q : Nat → Bool) : valuationOf q 1625 = false ∨ valuationOf q 1627 = true := by
  have hs : count1626 q = (countLit q [-110, -113]) + (countLit q [-114, -116]) := List.countP_append (p := literal q) (l₁ := [-110, -113]) (l₂ := [-114, -116])
  have hm := merge_right (literal (valuationOf q) (1625)) (literal (valuationOf q) (1627)) (countLit q [-110, -113]) (countLit q [-114, -116]) (count1626 q) 2 (meaning1625 q) (meaning1627 q) hs
  change valuationOf q 1625 = false ∨ valuationOf q 1627 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1286 (q : Snake 81) (h : Conditions q) : valuation q 1625 = false ∨ valuation q 1627 = true := counterClause1286 (baseVal q)

theorem counterClause1287 (q : Nat → Bool) : valuationOf q 1622 = false ∨ valuationOf q 1626 = true := by
  have hs : count1626 q = (countLit q [-110, -113]) + (countLit q [-114, -116]) := List.countP_append (p := literal q) (l₁ := [-110, -113]) (l₂ := [-114, -116])
  have hm := merge_left (literal (valuationOf q) (1622)) (literal (valuationOf q) (1626)) (countLit q [-110, -113]) (countLit q [-114, -116]) (count1626 q) 1 (meaning1622 q) (meaning1626 q) hs
  change valuationOf q 1622 = false ∨ valuationOf q 1626 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1287 (q : Snake 81) (h : Conditions q) : valuation q 1622 = false ∨ valuation q 1626 = true := counterClause1287 (baseVal q)

theorem counterClause1288 (q : Nat → Bool) : valuationOf q 1622 = false ∨ valuationOf q 1624 = false ∨ valuationOf q 1627 = true := by
  have hs : count1626 q = (countLit q [-110, -113]) + (countLit q [-114, -116]) := List.countP_append (p := literal q) (l₁ := [-110, -113]) (l₂ := [-114, -116])
  have hm := merge_two (literal (valuationOf q) (1622)) (literal (valuationOf q) (1624)) (literal (valuationOf q) (1627)) (countLit q [-110, -113]) (countLit q [-114, -116]) (count1626 q) 1 1 (meaning1622 q) (meaning1624 q) (meaning1627 q) hs
  change valuationOf q 1622 = false ∨ valuationOf q 1624 = false ∨ valuationOf q 1627 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1288 (q : Snake 81) (h : Conditions q) : valuation q 1622 = false ∨ valuation q 1624 = false ∨ valuation q 1627 = true := counterClause1288 (baseVal q)

theorem counterClause1289 (q : Nat → Bool) : valuationOf q 1622 = false ∨ valuationOf q 1625 = false ∨ valuationOf q 1628 = true := by
  have hs : count1626 q = (countLit q [-110, -113]) + (countLit q [-114, -116]) := List.countP_append (p := literal q) (l₁ := [-110, -113]) (l₂ := [-114, -116])
  have hm := merge_two (literal (valuationOf q) (1622)) (literal (valuationOf q) (1625)) (literal (valuationOf q) (1628)) (countLit q [-110, -113]) (countLit q [-114, -116]) (count1626 q) 1 2 (meaning1622 q) (meaning1625 q) (meaning1628 q) hs
  change valuationOf q 1622 = false ∨ valuationOf q 1625 = false ∨ valuationOf q 1628 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1289 (q : Snake 81) (h : Conditions q) : valuation q 1622 = false ∨ valuation q 1625 = false ∨ valuation q 1628 = true := counterClause1289 (baseVal q)

theorem counterClause1290 (q : Nat → Bool) : valuationOf q 1623 = false ∨ valuationOf q 1627 = true := by
  have hs : count1626 q = (countLit q [-110, -113]) + (countLit q [-114, -116]) := List.countP_append (p := literal q) (l₁ := [-110, -113]) (l₂ := [-114, -116])
  have hm := merge_left (literal (valuationOf q) (1623)) (literal (valuationOf q) (1627)) (countLit q [-110, -113]) (countLit q [-114, -116]) (count1626 q) 2 (meaning1623 q) (meaning1627 q) hs
  change valuationOf q 1623 = false ∨ valuationOf q 1627 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1290 (q : Snake 81) (h : Conditions q) : valuation q 1623 = false ∨ valuation q 1627 = true := counterClause1290 (baseVal q)

theorem counterClause1291 (q : Nat → Bool) : valuationOf q 1623 = false ∨ valuationOf q 1624 = false ∨ valuationOf q 1628 = true := by
  have hs : count1626 q = (countLit q [-110, -113]) + (countLit q [-114, -116]) := List.countP_append (p := literal q) (l₁ := [-110, -113]) (l₂ := [-114, -116])
  have hm := merge_two (literal (valuationOf q) (1623)) (literal (valuationOf q) (1624)) (literal (valuationOf q) (1628)) (countLit q [-110, -113]) (countLit q [-114, -116]) (count1626 q) 2 1 (meaning1623 q) (meaning1624 q) (meaning1628 q) hs
  change valuationOf q 1623 = false ∨ valuationOf q 1624 = false ∨ valuationOf q 1628 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1291 (q : Snake 81) (h : Conditions q) : valuation q 1623 = false ∨ valuation q 1624 = false ∨ valuation q 1628 = true := counterClause1291 (baseVal q)

theorem counterClause1292 (q : Nat → Bool) : valuationOf q 1623 = false ∨ valuationOf q 1625 = false ∨ valuationOf q 1629 = true := by
  have hs : count1626 q = (countLit q [-110, -113]) + (countLit q [-114, -116]) := List.countP_append (p := literal q) (l₁ := [-110, -113]) (l₂ := [-114, -116])
  have hm := merge_two (literal (valuationOf q) (1623)) (literal (valuationOf q) (1625)) (literal (valuationOf q) (1629)) (countLit q [-110, -113]) (countLit q [-114, -116]) (count1626 q) 2 2 (meaning1623 q) (meaning1625 q) (meaning1629 q) hs
  change valuationOf q 1623 = false ∨ valuationOf q 1625 = false ∨ valuationOf q 1629 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1292 (q : Snake 81) (h : Conditions q) : valuation q 1623 = false ∨ valuation q 1625 = false ∨ valuation q 1629 = true := counterClause1292 (baseVal q)

theorem counterClause1293 (q : Nat → Bool) : valuationOf q 1626 = false ∨ valuationOf q 1630 = true := by
  have hs : count1630 q = (countLit q [-103, -104, -105, -106]) + (countLit q [-110, -113, -114, -116]) := List.countP_append (p := literal q) (l₁ := [-103, -104, -105, -106]) (l₂ := [-110, -113, -114, -116])
  have hm := merge_right (literal (valuationOf q) (1626)) (literal (valuationOf q) (1630)) (countLit q [-103, -104, -105, -106]) (countLit q [-110, -113, -114, -116]) (count1630 q) 1 (meaning1626 q) (meaning1630 q) hs
  change valuationOf q 1626 = false ∨ valuationOf q 1630 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1293 (q : Snake 81) (h : Conditions q) : valuation q 1626 = false ∨ valuation q 1630 = true := counterClause1293 (baseVal q)

theorem counterClause1294 (q : Nat → Bool) : valuationOf q 1627 = false ∨ valuationOf q 1631 = true := by
  have hs : count1630 q = (countLit q [-103, -104, -105, -106]) + (countLit q [-110, -113, -114, -116]) := List.countP_append (p := literal q) (l₁ := [-103, -104, -105, -106]) (l₂ := [-110, -113, -114, -116])
  have hm := merge_right (literal (valuationOf q) (1627)) (literal (valuationOf q) (1631)) (countLit q [-103, -104, -105, -106]) (countLit q [-110, -113, -114, -116]) (count1630 q) 2 (meaning1627 q) (meaning1631 q) hs
  change valuationOf q 1627 = false ∨ valuationOf q 1631 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1294 (q : Snake 81) (h : Conditions q) : valuation q 1627 = false ∨ valuation q 1631 = true := counterClause1294 (baseVal q)

theorem counterClause1295 (q : Nat → Bool) : valuationOf q 1628 = false ∨ valuationOf q 1632 = true := by
  have hs : count1630 q = (countLit q [-103, -104, -105, -106]) + (countLit q [-110, -113, -114, -116]) := List.countP_append (p := literal q) (l₁ := [-103, -104, -105, -106]) (l₂ := [-110, -113, -114, -116])
  have hm := merge_right (literal (valuationOf q) (1628)) (literal (valuationOf q) (1632)) (countLit q [-103, -104, -105, -106]) (countLit q [-110, -113, -114, -116]) (count1630 q) 3 (meaning1628 q) (meaning1632 q) hs
  change valuationOf q 1628 = false ∨ valuationOf q 1632 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1295 (q : Snake 81) (h : Conditions q) : valuation q 1628 = false ∨ valuation q 1632 = true := counterClause1295 (baseVal q)

theorem counterClause1296 (q : Nat → Bool) : valuationOf q 1629 = false ∨ valuationOf q 1633 = true := by
  have hs : count1630 q = (countLit q [-103, -104, -105, -106]) + (countLit q [-110, -113, -114, -116]) := List.countP_append (p := literal q) (l₁ := [-103, -104, -105, -106]) (l₂ := [-110, -113, -114, -116])
  have hm := merge_right (literal (valuationOf q) (1629)) (literal (valuationOf q) (1633)) (countLit q [-103, -104, -105, -106]) (countLit q [-110, -113, -114, -116]) (count1630 q) 4 (meaning1629 q) (meaning1633 q) hs
  change valuationOf q 1629 = false ∨ valuationOf q 1633 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1296 (q : Snake 81) (h : Conditions q) : valuation q 1629 = false ∨ valuation q 1633 = true := counterClause1296 (baseVal q)

theorem counterClause1297 (q : Nat → Bool) : valuationOf q 1618 = false ∨ valuationOf q 1630 = true := by
  have hs : count1630 q = (countLit q [-103, -104, -105, -106]) + (countLit q [-110, -113, -114, -116]) := List.countP_append (p := literal q) (l₁ := [-103, -104, -105, -106]) (l₂ := [-110, -113, -114, -116])
  have hm := merge_left (literal (valuationOf q) (1618)) (literal (valuationOf q) (1630)) (countLit q [-103, -104, -105, -106]) (countLit q [-110, -113, -114, -116]) (count1630 q) 1 (meaning1618 q) (meaning1630 q) hs
  change valuationOf q 1618 = false ∨ valuationOf q 1630 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1297 (q : Snake 81) (h : Conditions q) : valuation q 1618 = false ∨ valuation q 1630 = true := counterClause1297 (baseVal q)

theorem counterClause1298 (q : Nat → Bool) : valuationOf q 1618 = false ∨ valuationOf q 1626 = false ∨ valuationOf q 1631 = true := by
  have hs : count1630 q = (countLit q [-103, -104, -105, -106]) + (countLit q [-110, -113, -114, -116]) := List.countP_append (p := literal q) (l₁ := [-103, -104, -105, -106]) (l₂ := [-110, -113, -114, -116])
  have hm := merge_two (literal (valuationOf q) (1618)) (literal (valuationOf q) (1626)) (literal (valuationOf q) (1631)) (countLit q [-103, -104, -105, -106]) (countLit q [-110, -113, -114, -116]) (count1630 q) 1 1 (meaning1618 q) (meaning1626 q) (meaning1631 q) hs
  change valuationOf q 1618 = false ∨ valuationOf q 1626 = false ∨ valuationOf q 1631 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1298 (q : Snake 81) (h : Conditions q) : valuation q 1618 = false ∨ valuation q 1626 = false ∨ valuation q 1631 = true := counterClause1298 (baseVal q)

theorem counterClause1299 (q : Nat → Bool) : valuationOf q 1618 = false ∨ valuationOf q 1627 = false ∨ valuationOf q 1632 = true := by
  have hs : count1630 q = (countLit q [-103, -104, -105, -106]) + (countLit q [-110, -113, -114, -116]) := List.countP_append (p := literal q) (l₁ := [-103, -104, -105, -106]) (l₂ := [-110, -113, -114, -116])
  have hm := merge_two (literal (valuationOf q) (1618)) (literal (valuationOf q) (1627)) (literal (valuationOf q) (1632)) (countLit q [-103, -104, -105, -106]) (countLit q [-110, -113, -114, -116]) (count1630 q) 1 2 (meaning1618 q) (meaning1627 q) (meaning1632 q) hs
  change valuationOf q 1618 = false ∨ valuationOf q 1627 = false ∨ valuationOf q 1632 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1299 (q : Snake 81) (h : Conditions q) : valuation q 1618 = false ∨ valuation q 1627 = false ∨ valuation q 1632 = true := counterClause1299 (baseVal q)

theorem counterClause1300 (q : Nat → Bool) : valuationOf q 1618 = false ∨ valuationOf q 1628 = false ∨ valuationOf q 1633 = true := by
  have hs : count1630 q = (countLit q [-103, -104, -105, -106]) + (countLit q [-110, -113, -114, -116]) := List.countP_append (p := literal q) (l₁ := [-103, -104, -105, -106]) (l₂ := [-110, -113, -114, -116])
  have hm := merge_two (literal (valuationOf q) (1618)) (literal (valuationOf q) (1628)) (literal (valuationOf q) (1633)) (countLit q [-103, -104, -105, -106]) (countLit q [-110, -113, -114, -116]) (count1630 q) 1 3 (meaning1618 q) (meaning1628 q) (meaning1633 q) hs
  change valuationOf q 1618 = false ∨ valuationOf q 1628 = false ∨ valuationOf q 1633 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1300 (q : Snake 81) (h : Conditions q) : valuation q 1618 = false ∨ valuation q 1628 = false ∨ valuation q 1633 = true := counterClause1300 (baseVal q)

theorem counterClause1301 (q : Nat → Bool) : valuationOf q 1618 = false ∨ valuationOf q 1629 = false ∨ valuationOf q 1634 = true := by
  have hs : count1630 q = (countLit q [-103, -104, -105, -106]) + (countLit q [-110, -113, -114, -116]) := List.countP_append (p := literal q) (l₁ := [-103, -104, -105, -106]) (l₂ := [-110, -113, -114, -116])
  have hm := merge_two (literal (valuationOf q) (1618)) (literal (valuationOf q) (1629)) (literal (valuationOf q) (1634)) (countLit q [-103, -104, -105, -106]) (countLit q [-110, -113, -114, -116]) (count1630 q) 1 4 (meaning1618 q) (meaning1629 q) (meaning1634 q) hs
  change valuationOf q 1618 = false ∨ valuationOf q 1629 = false ∨ valuationOf q 1634 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1301 (q : Snake 81) (h : Conditions q) : valuation q 1618 = false ∨ valuation q 1629 = false ∨ valuation q 1634 = true := counterClause1301 (baseVal q)

theorem counterClause1302 (q : Nat → Bool) : valuationOf q 1619 = false ∨ valuationOf q 1631 = true := by
  have hs : count1630 q = (countLit q [-103, -104, -105, -106]) + (countLit q [-110, -113, -114, -116]) := List.countP_append (p := literal q) (l₁ := [-103, -104, -105, -106]) (l₂ := [-110, -113, -114, -116])
  have hm := merge_left (literal (valuationOf q) (1619)) (literal (valuationOf q) (1631)) (countLit q [-103, -104, -105, -106]) (countLit q [-110, -113, -114, -116]) (count1630 q) 2 (meaning1619 q) (meaning1631 q) hs
  change valuationOf q 1619 = false ∨ valuationOf q 1631 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1302 (q : Snake 81) (h : Conditions q) : valuation q 1619 = false ∨ valuation q 1631 = true := counterClause1302 (baseVal q)

theorem counterClause1303 (q : Nat → Bool) : valuationOf q 1619 = false ∨ valuationOf q 1626 = false ∨ valuationOf q 1632 = true := by
  have hs : count1630 q = (countLit q [-103, -104, -105, -106]) + (countLit q [-110, -113, -114, -116]) := List.countP_append (p := literal q) (l₁ := [-103, -104, -105, -106]) (l₂ := [-110, -113, -114, -116])
  have hm := merge_two (literal (valuationOf q) (1619)) (literal (valuationOf q) (1626)) (literal (valuationOf q) (1632)) (countLit q [-103, -104, -105, -106]) (countLit q [-110, -113, -114, -116]) (count1630 q) 2 1 (meaning1619 q) (meaning1626 q) (meaning1632 q) hs
  change valuationOf q 1619 = false ∨ valuationOf q 1626 = false ∨ valuationOf q 1632 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1303 (q : Snake 81) (h : Conditions q) : valuation q 1619 = false ∨ valuation q 1626 = false ∨ valuation q 1632 = true := counterClause1303 (baseVal q)

theorem counterClause1304 (q : Nat → Bool) : valuationOf q 1619 = false ∨ valuationOf q 1627 = false ∨ valuationOf q 1633 = true := by
  have hs : count1630 q = (countLit q [-103, -104, -105, -106]) + (countLit q [-110, -113, -114, -116]) := List.countP_append (p := literal q) (l₁ := [-103, -104, -105, -106]) (l₂ := [-110, -113, -114, -116])
  have hm := merge_two (literal (valuationOf q) (1619)) (literal (valuationOf q) (1627)) (literal (valuationOf q) (1633)) (countLit q [-103, -104, -105, -106]) (countLit q [-110, -113, -114, -116]) (count1630 q) 2 2 (meaning1619 q) (meaning1627 q) (meaning1633 q) hs
  change valuationOf q 1619 = false ∨ valuationOf q 1627 = false ∨ valuationOf q 1633 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1304 (q : Snake 81) (h : Conditions q) : valuation q 1619 = false ∨ valuation q 1627 = false ∨ valuation q 1633 = true := counterClause1304 (baseVal q)

theorem counterClause1305 (q : Nat → Bool) : valuationOf q 1619 = false ∨ valuationOf q 1628 = false ∨ valuationOf q 1634 = true := by
  have hs : count1630 q = (countLit q [-103, -104, -105, -106]) + (countLit q [-110, -113, -114, -116]) := List.countP_append (p := literal q) (l₁ := [-103, -104, -105, -106]) (l₂ := [-110, -113, -114, -116])
  have hm := merge_two (literal (valuationOf q) (1619)) (literal (valuationOf q) (1628)) (literal (valuationOf q) (1634)) (countLit q [-103, -104, -105, -106]) (countLit q [-110, -113, -114, -116]) (count1630 q) 2 3 (meaning1619 q) (meaning1628 q) (meaning1634 q) hs
  change valuationOf q 1619 = false ∨ valuationOf q 1628 = false ∨ valuationOf q 1634 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1305 (q : Snake 81) (h : Conditions q) : valuation q 1619 = false ∨ valuation q 1628 = false ∨ valuation q 1634 = true := counterClause1305 (baseVal q)

theorem counterClause1306 (q : Nat → Bool) : valuationOf q 1620 = false ∨ valuationOf q 1632 = true := by
  have hs : count1630 q = (countLit q [-103, -104, -105, -106]) + (countLit q [-110, -113, -114, -116]) := List.countP_append (p := literal q) (l₁ := [-103, -104, -105, -106]) (l₂ := [-110, -113, -114, -116])
  have hm := merge_left (literal (valuationOf q) (1620)) (literal (valuationOf q) (1632)) (countLit q [-103, -104, -105, -106]) (countLit q [-110, -113, -114, -116]) (count1630 q) 3 (meaning1620 q) (meaning1632 q) hs
  change valuationOf q 1620 = false ∨ valuationOf q 1632 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1306 (q : Snake 81) (h : Conditions q) : valuation q 1620 = false ∨ valuation q 1632 = true := counterClause1306 (baseVal q)

theorem counterClause1307 (q : Nat → Bool) : valuationOf q 1620 = false ∨ valuationOf q 1626 = false ∨ valuationOf q 1633 = true := by
  have hs : count1630 q = (countLit q [-103, -104, -105, -106]) + (countLit q [-110, -113, -114, -116]) := List.countP_append (p := literal q) (l₁ := [-103, -104, -105, -106]) (l₂ := [-110, -113, -114, -116])
  have hm := merge_two (literal (valuationOf q) (1620)) (literal (valuationOf q) (1626)) (literal (valuationOf q) (1633)) (countLit q [-103, -104, -105, -106]) (countLit q [-110, -113, -114, -116]) (count1630 q) 3 1 (meaning1620 q) (meaning1626 q) (meaning1633 q) hs
  change valuationOf q 1620 = false ∨ valuationOf q 1626 = false ∨ valuationOf q 1633 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1307 (q : Snake 81) (h : Conditions q) : valuation q 1620 = false ∨ valuation q 1626 = false ∨ valuation q 1633 = true := counterClause1307 (baseVal q)

theorem counterClause1308 (q : Nat → Bool) : valuationOf q 1630 = false ∨ valuationOf q 1638 = true := by
  have hs : count1638 q = (countLit q [-89, -90, -91, -92, -96, -97, -99]) + (countLit q [-103, -104, -105, -106, -110, -113, -114, -116]) := List.countP_append (p := literal q) (l₁ := [-89, -90, -91, -92, -96, -97, -99]) (l₂ := [-103, -104, -105, -106, -110, -113, -114, -116])
  have hm := merge_right (literal (valuationOf q) (1630)) (literal (valuationOf q) (1638)) (countLit q [-89, -90, -91, -92, -96, -97, -99]) (countLit q [-103, -104, -105, -106, -110, -113, -114, -116]) (count1638 q) 1 (meaning1630 q) (meaning1638 q) hs
  change valuationOf q 1630 = false ∨ valuationOf q 1638 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1308 (q : Snake 81) (h : Conditions q) : valuation q 1630 = false ∨ valuation q 1638 = true := counterClause1308 (baseVal q)

theorem counterClause1309 (q : Nat → Bool) : valuationOf q 1631 = false ∨ valuationOf q 1639 = true := by
  have hs : count1638 q = (countLit q [-89, -90, -91, -92, -96, -97, -99]) + (countLit q [-103, -104, -105, -106, -110, -113, -114, -116]) := List.countP_append (p := literal q) (l₁ := [-89, -90, -91, -92, -96, -97, -99]) (l₂ := [-103, -104, -105, -106, -110, -113, -114, -116])
  have hm := merge_right (literal (valuationOf q) (1631)) (literal (valuationOf q) (1639)) (countLit q [-89, -90, -91, -92, -96, -97, -99]) (countLit q [-103, -104, -105, -106, -110, -113, -114, -116]) (count1638 q) 2 (meaning1631 q) (meaning1639 q) hs
  change valuationOf q 1631 = false ∨ valuationOf q 1639 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1309 (q : Snake 81) (h : Conditions q) : valuation q 1631 = false ∨ valuation q 1639 = true := counterClause1309 (baseVal q)

theorem counterClause1310 (q : Nat → Bool) : valuationOf q 1632 = false ∨ valuationOf q 1640 = true := by
  have hs : count1638 q = (countLit q [-89, -90, -91, -92, -96, -97, -99]) + (countLit q [-103, -104, -105, -106, -110, -113, -114, -116]) := List.countP_append (p := literal q) (l₁ := [-89, -90, -91, -92, -96, -97, -99]) (l₂ := [-103, -104, -105, -106, -110, -113, -114, -116])
  have hm := merge_right (literal (valuationOf q) (1632)) (literal (valuationOf q) (1640)) (countLit q [-89, -90, -91, -92, -96, -97, -99]) (countLit q [-103, -104, -105, -106, -110, -113, -114, -116]) (count1638 q) 3 (meaning1632 q) (meaning1640 q) hs
  change valuationOf q 1632 = false ∨ valuationOf q 1640 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1310 (q : Snake 81) (h : Conditions q) : valuation q 1632 = false ∨ valuation q 1640 = true := counterClause1310 (baseVal q)

theorem counterClause1311 (q : Nat → Bool) : valuationOf q 1633 = false ∨ valuationOf q 1641 = true := by
  have hs : count1638 q = (countLit q [-89, -90, -91, -92, -96, -97, -99]) + (countLit q [-103, -104, -105, -106, -110, -113, -114, -116]) := List.countP_append (p := literal q) (l₁ := [-89, -90, -91, -92, -96, -97, -99]) (l₂ := [-103, -104, -105, -106, -110, -113, -114, -116])
  have hm := merge_right (literal (valuationOf q) (1633)) (literal (valuationOf q) (1641)) (countLit q [-89, -90, -91, -92, -96, -97, -99]) (countLit q [-103, -104, -105, -106, -110, -113, -114, -116]) (count1638 q) 4 (meaning1633 q) (meaning1641 q) hs
  change valuationOf q 1633 = false ∨ valuationOf q 1641 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1311 (q : Snake 81) (h : Conditions q) : valuation q 1633 = false ∨ valuation q 1641 = true := counterClause1311 (baseVal q)

theorem counterClause1312 (q : Nat → Bool) : valuationOf q 1634 = false ∨ valuationOf q 1642 = true := by
  have hs : count1638 q = (countLit q [-89, -90, -91, -92, -96, -97, -99]) + (countLit q [-103, -104, -105, -106, -110, -113, -114, -116]) := List.countP_append (p := literal q) (l₁ := [-89, -90, -91, -92, -96, -97, -99]) (l₂ := [-103, -104, -105, -106, -110, -113, -114, -116])
  have hm := merge_right (literal (valuationOf q) (1634)) (literal (valuationOf q) (1642)) (countLit q [-89, -90, -91, -92, -96, -97, -99]) (countLit q [-103, -104, -105, -106, -110, -113, -114, -116]) (count1638 q) 5 (meaning1634 q) (meaning1642 q) hs
  change valuationOf q 1634 = false ∨ valuationOf q 1642 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1312 (q : Snake 81) (h : Conditions q) : valuation q 1634 = false ∨ valuation q 1642 = true := counterClause1312 (baseVal q)

theorem block40 (q : Snake 81) (h : Conditions q) : B112E064.Block40 (valuation q) :=
  ⟨clause1281 q h, clause1282 q h, clause1283 q h, clause1284 q h, clause1285 q h, clause1286 q h, clause1287 q h, clause1288 q h, clause1289 q h, clause1290 q h, clause1291 q h, clause1292 q h, clause1293 q h, clause1294 q h, clause1295 q h, clause1296 q h, clause1297 q h, clause1298 q h, clause1299 q h, clause1300 q h, clause1301 q h, clause1302 q h, clause1303 q h, clause1304 q h, clause1305 q h, clause1306 q h, clause1307 q h, clause1308 q h, clause1309 q h, clause1310 q h, clause1311 q h, clause1312 q h⟩

end
end Snake9.Regrowth.E112064
