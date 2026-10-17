import E112064Semantics
import B112E064Inputs
namespace Snake9.Regrowth.E112064
noncomputable section
local instance blockDec39 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1249 (q : Nat → Bool) : valuationOf q 1553 = false ∨ valuationOf q 1573 = false ∨ valuationOf q 1587 = true := by
  have hs : count1579 q = (countLit q [-59, -60, -62, -65, -66, -68, -70]) + (countLit q [-72, -74, -76, -78, -81, -82, -83, -86]) := List.countP_append (p := literal q) (l₁ := [-59, -60, -62, -65, -66, -68, -70]) (l₂ := [-72, -74, -76, -78, -81, -82, -83, -86])
  have hm := merge_two (literal (valuationOf q) (1553)) (literal (valuationOf q) (1573)) (literal (valuationOf q) (1587)) (countLit q [-59, -60, -62, -65, -66, -68, -70]) (countLit q [-72, -74, -76, -78, -81, -82, -83, -86]) (count1579 q) 6 3 (meaning1553 q) (meaning1573 q) (meaning1587 q) hs
  change valuationOf q 1553 = false ∨ valuationOf q 1573 = false ∨ valuationOf q 1587 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1249 (q : Snake 81) (h : Conditions q) : valuation q 1553 = false ∨ valuation q 1573 = false ∨ valuation q 1587 = true := counterClause1249 (baseVal q)

theorem counterClause1250 (q : Nat → Bool) : valuationOf q 1553 = false ∨ valuationOf q 1574 = false ∨ valuationOf q 1588 = true := by
  have hs : count1579 q = (countLit q [-59, -60, -62, -65, -66, -68, -70]) + (countLit q [-72, -74, -76, -78, -81, -82, -83, -86]) := List.countP_append (p := literal q) (l₁ := [-59, -60, -62, -65, -66, -68, -70]) (l₂ := [-72, -74, -76, -78, -81, -82, -83, -86])
  have hm := merge_two (literal (valuationOf q) (1553)) (literal (valuationOf q) (1574)) (literal (valuationOf q) (1588)) (countLit q [-59, -60, -62, -65, -66, -68, -70]) (countLit q [-72, -74, -76, -78, -81, -82, -83, -86]) (count1579 q) 6 4 (meaning1553 q) (meaning1574 q) (meaning1588 q) hs
  change valuationOf q 1553 = false ∨ valuationOf q 1574 = false ∨ valuationOf q 1588 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1250 (q : Snake 81) (h : Conditions q) : valuation q 1553 = false ∨ valuation q 1574 = false ∨ valuation q 1588 = true := counterClause1250 (baseVal q)

theorem counterClause1251 (q : Nat → Bool) : valuationOf q 90 = true ∨ valuationOf q 1594 = true := by
  have hs : count1594 q = (countLit q [-90]) + (countLit q [-91]) := List.countP_append (p := literal q) (l₁ := [-90]) (l₂ := [-91])
  have hm := merge_left (literal (valuationOf q) (-90)) (literal (valuationOf q) (1594)) (countLit q [-90]) (countLit q [-91]) (count1594 q) 1 (meaningNeg90 q) (meaning1594 q) hs
  change (! (valuationOf q 90)) = false ∨ valuationOf q 1594 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1251 (q : Snake 81) (h : Conditions q) : valuation q 90 = true ∨ valuation q 1594 = true := counterClause1251 (baseVal q)

theorem counterClause1252 (q : Nat → Bool) : valuationOf q 1594 = false ∨ valuationOf q 1596 = true := by
  have hs : count1596 q = (countLit q [-89]) + (countLit q [-90, -91]) := List.countP_append (p := literal q) (l₁ := [-89]) (l₂ := [-90, -91])
  have hm := merge_right (literal (valuationOf q) (1594)) (literal (valuationOf q) (1596)) (countLit q [-89]) (countLit q [-90, -91]) (count1596 q) 1 (meaning1594 q) (meaning1596 q) hs
  change valuationOf q 1594 = false ∨ valuationOf q 1596 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1252 (q : Snake 81) (h : Conditions q) : valuation q 1594 = false ∨ valuation q 1596 = true := counterClause1252 (baseVal q)

theorem counterClause1253 (q : Nat → Bool) : valuationOf q 89 = true ∨ valuationOf q 1596 = true := by
  have hs : count1596 q = (countLit q [-89]) + (countLit q [-90, -91]) := List.countP_append (p := literal q) (l₁ := [-89]) (l₂ := [-90, -91])
  have hm := merge_left (literal (valuationOf q) (-89)) (literal (valuationOf q) (1596)) (countLit q [-89]) (countLit q [-90, -91]) (count1596 q) 1 (meaningNeg89 q) (meaning1596 q) hs
  change (! (valuationOf q 89)) = false ∨ valuationOf q 1596 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1253 (q : Snake 81) (h : Conditions q) : valuation q 89 = true ∨ valuation q 1596 = true := counterClause1253 (baseVal q)

theorem counterClause1254 (q : Nat → Bool) : valuationOf q 89 = true ∨ valuationOf q 1594 = false ∨ valuationOf q 1597 = true := by
  have hs : count1596 q = (countLit q [-89]) + (countLit q [-90, -91]) := List.countP_append (p := literal q) (l₁ := [-89]) (l₂ := [-90, -91])
  have hm := merge_two (literal (valuationOf q) (-89)) (literal (valuationOf q) (1594)) (literal (valuationOf q) (1597)) (countLit q [-89]) (countLit q [-90, -91]) (count1596 q) 1 1 (meaningNeg89 q) (meaning1594 q) (meaning1597 q) hs
  change (! (valuationOf q 89)) = false ∨ valuationOf q 1594 = false ∨ valuationOf q 1597 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1254 (q : Snake 81) (h : Conditions q) : valuation q 89 = true ∨ valuation q 1594 = false ∨ valuation q 1597 = true := counterClause1254 (baseVal q)

theorem counterClause1255 (q : Nat → Bool) : valuationOf q 96 = true ∨ valuationOf q 1599 = true := by
  have hs : count1599 q = (countLit q [-92]) + (countLit q [-96]) := List.countP_append (p := literal q) (l₁ := [-92]) (l₂ := [-96])
  have hm := merge_right (literal (valuationOf q) (-96)) (literal (valuationOf q) (1599)) (countLit q [-92]) (countLit q [-96]) (count1599 q) 1 (meaningNeg96 q) (meaning1599 q) hs
  change (! (valuationOf q 96)) = false ∨ valuationOf q 1599 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1255 (q : Snake 81) (h : Conditions q) : valuation q 96 = true ∨ valuation q 1599 = true := counterClause1255 (baseVal q)

theorem counterClause1256 (q : Nat → Bool) : valuationOf q 92 = true ∨ valuationOf q 1599 = true := by
  have hs : count1599 q = (countLit q [-92]) + (countLit q [-96]) := List.countP_append (p := literal q) (l₁ := [-92]) (l₂ := [-96])
  have hm := merge_left (literal (valuationOf q) (-92)) (literal (valuationOf q) (1599)) (countLit q [-92]) (countLit q [-96]) (count1599 q) 1 (meaningNeg92 q) (meaning1599 q) hs
  change (! (valuationOf q 92)) = false ∨ valuationOf q 1599 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1256 (q : Snake 81) (h : Conditions q) : valuation q 92 = true ∨ valuation q 1599 = true := counterClause1256 (baseVal q)

theorem counterClause1257 (q : Nat → Bool) : valuationOf q 99 = true ∨ valuationOf q 1601 = true := by
  have hs : count1601 q = (countLit q [-97]) + (countLit q [-99]) := List.countP_append (p := literal q) (l₁ := [-97]) (l₂ := [-99])
  have hm := merge_right (literal (valuationOf q) (-99)) (literal (valuationOf q) (1601)) (countLit q [-97]) (countLit q [-99]) (count1601 q) 1 (meaningNeg99 q) (meaning1601 q) hs
  change (! (valuationOf q 99)) = false ∨ valuationOf q 1601 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1257 (q : Snake 81) (h : Conditions q) : valuation q 99 = true ∨ valuation q 1601 = true := counterClause1257 (baseVal q)

theorem counterClause1258 (q : Nat → Bool) : valuationOf q 1601 = false ∨ valuationOf q 1603 = true := by
  have hs : count1603 q = (countLit q [-92, -96]) + (countLit q [-97, -99]) := List.countP_append (p := literal q) (l₁ := [-92, -96]) (l₂ := [-97, -99])
  have hm := merge_right (literal (valuationOf q) (1601)) (literal (valuationOf q) (1603)) (countLit q [-92, -96]) (countLit q [-97, -99]) (count1603 q) 1 (meaning1601 q) (meaning1603 q) hs
  change valuationOf q 1601 = false ∨ valuationOf q 1603 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1258 (q : Snake 81) (h : Conditions q) : valuation q 1601 = false ∨ valuation q 1603 = true := counterClause1258 (baseVal q)

theorem counterClause1259 (q : Nat → Bool) : valuationOf q 1599 = false ∨ valuationOf q 1603 = true := by
  have hs : count1603 q = (countLit q [-92, -96]) + (countLit q [-97, -99]) := List.countP_append (p := literal q) (l₁ := [-92, -96]) (l₂ := [-97, -99])
  have hm := merge_left (literal (valuationOf q) (1599)) (literal (valuationOf q) (1603)) (countLit q [-92, -96]) (countLit q [-97, -99]) (count1603 q) 1 (meaning1599 q) (meaning1603 q) hs
  change valuationOf q 1599 = false ∨ valuationOf q 1603 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1259 (q : Snake 81) (h : Conditions q) : valuation q 1599 = false ∨ valuation q 1603 = true := counterClause1259 (baseVal q)

theorem counterClause1260 (q : Nat → Bool) : valuationOf q 1599 = false ∨ valuationOf q 1601 = false ∨ valuationOf q 1604 = true := by
  have hs : count1603 q = (countLit q [-92, -96]) + (countLit q [-97, -99]) := List.countP_append (p := literal q) (l₁ := [-92, -96]) (l₂ := [-97, -99])
  have hm := merge_two (literal (valuationOf q) (1599)) (literal (valuationOf q) (1601)) (literal (valuationOf q) (1604)) (countLit q [-92, -96]) (countLit q [-97, -99]) (count1603 q) 1 1 (meaning1599 q) (meaning1601 q) (meaning1604 q) hs
  change valuationOf q 1599 = false ∨ valuationOf q 1601 = false ∨ valuationOf q 1604 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1260 (q : Snake 81) (h : Conditions q) : valuation q 1599 = false ∨ valuation q 1601 = false ∨ valuation q 1604 = true := counterClause1260 (baseVal q)

theorem counterClause1261 (q : Nat → Bool) : valuationOf q 1603 = false ∨ valuationOf q 1607 = true := by
  have hs : count1607 q = (countLit q [-89, -90, -91]) + (countLit q [-92, -96, -97, -99]) := List.countP_append (p := literal q) (l₁ := [-89, -90, -91]) (l₂ := [-92, -96, -97, -99])
  have hm := merge_right (literal (valuationOf q) (1603)) (literal (valuationOf q) (1607)) (countLit q [-89, -90, -91]) (countLit q [-92, -96, -97, -99]) (count1607 q) 1 (meaning1603 q) (meaning1607 q) hs
  change valuationOf q 1603 = false ∨ valuationOf q 1607 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1261 (q : Snake 81) (h : Conditions q) : valuation q 1603 = false ∨ valuation q 1607 = true := counterClause1261 (baseVal q)

theorem counterClause1262 (q : Nat → Bool) : valuationOf q 1604 = false ∨ valuationOf q 1608 = true := by
  have hs : count1607 q = (countLit q [-89, -90, -91]) + (countLit q [-92, -96, -97, -99]) := List.countP_append (p := literal q) (l₁ := [-89, -90, -91]) (l₂ := [-92, -96, -97, -99])
  have hm := merge_right (literal (valuationOf q) (1604)) (literal (valuationOf q) (1608)) (countLit q [-89, -90, -91]) (countLit q [-92, -96, -97, -99]) (count1607 q) 2 (meaning1604 q) (meaning1608 q) hs
  change valuationOf q 1604 = false ∨ valuationOf q 1608 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1262 (q : Snake 81) (h : Conditions q) : valuation q 1604 = false ∨ valuation q 1608 = true := counterClause1262 (baseVal q)

theorem counterClause1263 (q : Nat → Bool) : valuationOf q 1596 = false ∨ valuationOf q 1607 = true := by
  have hs : count1607 q = (countLit q [-89, -90, -91]) + (countLit q [-92, -96, -97, -99]) := List.countP_append (p := literal q) (l₁ := [-89, -90, -91]) (l₂ := [-92, -96, -97, -99])
  have hm := merge_left (literal (valuationOf q) (1596)) (literal (valuationOf q) (1607)) (countLit q [-89, -90, -91]) (countLit q [-92, -96, -97, -99]) (count1607 q) 1 (meaning1596 q) (meaning1607 q) hs
  change valuationOf q 1596 = false ∨ valuationOf q 1607 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1263 (q : Snake 81) (h : Conditions q) : valuation q 1596 = false ∨ valuation q 1607 = true := counterClause1263 (baseVal q)

theorem counterClause1264 (q : Nat → Bool) : valuationOf q 1596 = false ∨ valuationOf q 1604 = false ∨ valuationOf q 1609 = true := by
  have hs : count1607 q = (countLit q [-89, -90, -91]) + (countLit q [-92, -96, -97, -99]) := List.countP_append (p := literal q) (l₁ := [-89, -90, -91]) (l₂ := [-92, -96, -97, -99])
  have hm := merge_two (literal (valuationOf q) (1596)) (literal (valuationOf q) (1604)) (literal (valuationOf q) (1609)) (countLit q [-89, -90, -91]) (countLit q [-92, -96, -97, -99]) (count1607 q) 1 2 (meaning1596 q) (meaning1604 q) (meaning1609 q) hs
  change valuationOf q 1596 = false ∨ valuationOf q 1604 = false ∨ valuationOf q 1609 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1264 (q : Snake 81) (h : Conditions q) : valuation q 1596 = false ∨ valuation q 1604 = false ∨ valuation q 1609 = true := counterClause1264 (baseVal q)

theorem counterClause1265 (q : Nat → Bool) : valuationOf q 1597 = false ∨ valuationOf q 1604 = false ∨ valuationOf q 1610 = true := by
  have hs : count1607 q = (countLit q [-89, -90, -91]) + (countLit q [-92, -96, -97, -99]) := List.countP_append (p := literal q) (l₁ := [-89, -90, -91]) (l₂ := [-92, -96, -97, -99])
  have hm := merge_two (literal (valuationOf q) (1597)) (literal (valuationOf q) (1604)) (literal (valuationOf q) (1610)) (countLit q [-89, -90, -91]) (countLit q [-92, -96, -97, -99]) (count1607 q) 2 2 (meaning1597 q) (meaning1604 q) (meaning1610 q) hs
  change valuationOf q 1597 = false ∨ valuationOf q 1604 = false ∨ valuationOf q 1610 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1265 (q : Snake 81) (h : Conditions q) : valuation q 1597 = false ∨ valuation q 1604 = false ∨ valuation q 1610 = true := counterClause1265 (baseVal q)

theorem counterClause1266 (q : Nat → Bool) : valuationOf q 104 = true ∨ valuationOf q 1614 = true := by
  have hs : count1614 q = (countLit q [-103]) + (countLit q [-104]) := List.countP_append (p := literal q) (l₁ := [-103]) (l₂ := [-104])
  have hm := merge_right (literal (valuationOf q) (-104)) (literal (valuationOf q) (1614)) (countLit q [-103]) (countLit q [-104]) (count1614 q) 1 (meaningNeg104 q) (meaning1614 q) hs
  change (! (valuationOf q 104)) = false ∨ valuationOf q 1614 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1266 (q : Snake 81) (h : Conditions q) : valuation q 104 = true ∨ valuation q 1614 = true := counterClause1266 (baseVal q)

theorem counterClause1267 (q : Nat → Bool) : valuationOf q 103 = true ∨ valuationOf q 1614 = true := by
  have hs : count1614 q = (countLit q [-103]) + (countLit q [-104]) := List.countP_append (p := literal q) (l₁ := [-103]) (l₂ := [-104])
  have hm := merge_left (literal (valuationOf q) (-103)) (literal (valuationOf q) (1614)) (countLit q [-103]) (countLit q [-104]) (count1614 q) 1 (meaningNeg103 q) (meaning1614 q) hs
  change (! (valuationOf q 103)) = false ∨ valuationOf q 1614 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1267 (q : Snake 81) (h : Conditions q) : valuation q 103 = true ∨ valuation q 1614 = true := counterClause1267 (baseVal q)

theorem counterClause1268 (q : Nat → Bool) : valuationOf q 103 = true ∨ valuationOf q 104 = true ∨ valuationOf q 1615 = true := by
  have hs : count1614 q = (countLit q [-103]) + (countLit q [-104]) := List.countP_append (p := literal q) (l₁ := [-103]) (l₂ := [-104])
  have hm := merge_two (literal (valuationOf q) (-103)) (literal (valuationOf q) (-104)) (literal (valuationOf q) (1615)) (countLit q [-103]) (countLit q [-104]) (count1614 q) 1 1 (meaningNeg103 q) (meaningNeg104 q) (meaning1615 q) hs
  change (! (valuationOf q 103)) = false ∨ (! (valuationOf q 104)) = false ∨ valuationOf q 1615 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1268 (q : Snake 81) (h : Conditions q) : valuation q 103 = true ∨ valuation q 104 = true ∨ valuation q 1615 = true := counterClause1268 (baseVal q)

theorem counterClause1269 (q : Nat → Bool) : valuationOf q 106 = true ∨ valuationOf q 1616 = true := by
  have hs : count1616 q = (countLit q [-105]) + (countLit q [-106]) := List.countP_append (p := literal q) (l₁ := [-105]) (l₂ := [-106])
  have hm := merge_right (literal (valuationOf q) (-106)) (literal (valuationOf q) (1616)) (countLit q [-105]) (countLit q [-106]) (count1616 q) 1 (meaningNeg106 q) (meaning1616 q) hs
  change (! (valuationOf q 106)) = false ∨ valuationOf q 1616 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1269 (q : Snake 81) (h : Conditions q) : valuation q 106 = true ∨ valuation q 1616 = true := counterClause1269 (baseVal q)

theorem counterClause1270 (q : Nat → Bool) : valuationOf q 105 = true ∨ valuationOf q 1616 = true := by
  have hs : count1616 q = (countLit q [-105]) + (countLit q [-106]) := List.countP_append (p := literal q) (l₁ := [-105]) (l₂ := [-106])
  have hm := merge_left (literal (valuationOf q) (-105)) (literal (valuationOf q) (1616)) (countLit q [-105]) (countLit q [-106]) (count1616 q) 1 (meaningNeg105 q) (meaning1616 q) hs
  change (! (valuationOf q 105)) = false ∨ valuationOf q 1616 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1270 (q : Snake 81) (h : Conditions q) : valuation q 105 = true ∨ valuation q 1616 = true := counterClause1270 (baseVal q)

theorem counterClause1271 (q : Nat → Bool) : valuationOf q 105 = true ∨ valuationOf q 106 = true ∨ valuationOf q 1617 = true := by
  have hs : count1616 q = (countLit q [-105]) + (countLit q [-106]) := List.countP_append (p := literal q) (l₁ := [-105]) (l₂ := [-106])
  have hm := merge_two (literal (valuationOf q) (-105)) (literal (valuationOf q) (-106)) (literal (valuationOf q) (1617)) (countLit q [-105]) (countLit q [-106]) (count1616 q) 1 1 (meaningNeg105 q) (meaningNeg106 q) (meaning1617 q) hs
  change (! (valuationOf q 105)) = false ∨ (! (valuationOf q 106)) = false ∨ valuationOf q 1617 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1271 (q : Snake 81) (h : Conditions q) : valuation q 105 = true ∨ valuation q 106 = true ∨ valuation q 1617 = true := counterClause1271 (baseVal q)

theorem counterClause1272 (q : Nat → Bool) : valuationOf q 1616 = false ∨ valuationOf q 1618 = true := by
  have hs : count1618 q = (countLit q [-103, -104]) + (countLit q [-105, -106]) := List.countP_append (p := literal q) (l₁ := [-103, -104]) (l₂ := [-105, -106])
  have hm := merge_right (literal (valuationOf q) (1616)) (literal (valuationOf q) (1618)) (countLit q [-103, -104]) (countLit q [-105, -106]) (count1618 q) 1 (meaning1616 q) (meaning1618 q) hs
  change valuationOf q 1616 = false ∨ valuationOf q 1618 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1272 (q : Snake 81) (h : Conditions q) : valuation q 1616 = false ∨ valuation q 1618 = true := counterClause1272 (baseVal q)

theorem counterClause1273 (q : Nat → Bool) : valuationOf q 1617 = false ∨ valuationOf q 1619 = true := by
  have hs : count1618 q = (countLit q [-103, -104]) + (countLit q [-105, -106]) := List.countP_append (p := literal q) (l₁ := [-103, -104]) (l₂ := [-105, -106])
  have hm := merge_right (literal (valuationOf q) (1617)) (literal (valuationOf q) (1619)) (countLit q [-103, -104]) (countLit q [-105, -106]) (count1618 q) 2 (meaning1617 q) (meaning1619 q) hs
  change valuationOf q 1617 = false ∨ valuationOf q 1619 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1273 (q : Snake 81) (h : Conditions q) : valuation q 1617 = false ∨ valuation q 1619 = true := counterClause1273 (baseVal q)

theorem counterClause1274 (q : Nat → Bool) : valuationOf q 1614 = false ∨ valuationOf q 1618 = true := by
  have hs : count1618 q = (countLit q [-103, -104]) + (countLit q [-105, -106]) := List.countP_append (p := literal q) (l₁ := [-103, -104]) (l₂ := [-105, -106])
  have hm := merge_left (literal (valuationOf q) (1614)) (literal (valuationOf q) (1618)) (countLit q [-103, -104]) (countLit q [-105, -106]) (count1618 q) 1 (meaning1614 q) (meaning1618 q) hs
  change valuationOf q 1614 = false ∨ valuationOf q 1618 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1274 (q : Snake 81) (h : Conditions q) : valuation q 1614 = false ∨ valuation q 1618 = true := counterClause1274 (baseVal q)

theorem counterClause1275 (q : Nat → Bool) : valuationOf q 1614 = false ∨ valuationOf q 1616 = false ∨ valuationOf q 1619 = true := by
  have hs : count1618 q = (countLit q [-103, -104]) + (countLit q [-105, -106]) := List.countP_append (p := literal q) (l₁ := [-103, -104]) (l₂ := [-105, -106])
  have hm := merge_two (literal (valuationOf q) (1614)) (literal (valuationOf q) (1616)) (literal (valuationOf q) (1619)) (countLit q [-103, -104]) (countLit q [-105, -106]) (count1618 q) 1 1 (meaning1614 q) (meaning1616 q) (meaning1619 q) hs
  change valuationOf q 1614 = false ∨ valuationOf q 1616 = false ∨ valuationOf q 1619 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1275 (q : Snake 81) (h : Conditions q) : valuation q 1614 = false ∨ valuation q 1616 = false ∨ valuation q 1619 = true := counterClause1275 (baseVal q)

theorem counterClause1276 (q : Nat → Bool) : valuationOf q 1614 = false ∨ valuationOf q 1617 = false ∨ valuationOf q 1620 = true := by
  have hs : count1618 q = (countLit q [-103, -104]) + (countLit q [-105, -106]) := List.countP_append (p := literal q) (l₁ := [-103, -104]) (l₂ := [-105, -106])
  have hm := merge_two (literal (valuationOf q) (1614)) (literal (valuationOf q) (1617)) (literal (valuationOf q) (1620)) (countLit q [-103, -104]) (countLit q [-105, -106]) (count1618 q) 1 2 (meaning1614 q) (meaning1617 q) (meaning1620 q) hs
  change valuationOf q 1614 = false ∨ valuationOf q 1617 = false ∨ valuationOf q 1620 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1276 (q : Snake 81) (h : Conditions q) : valuation q 1614 = false ∨ valuation q 1617 = false ∨ valuation q 1620 = true := counterClause1276 (baseVal q)

theorem counterClause1277 (q : Nat → Bool) : valuationOf q 1615 = false ∨ valuationOf q 1619 = true := by
  have hs : count1618 q = (countLit q [-103, -104]) + (countLit q [-105, -106]) := List.countP_append (p := literal q) (l₁ := [-103, -104]) (l₂ := [-105, -106])
  have hm := merge_left (literal (valuationOf q) (1615)) (literal (valuationOf q) (1619)) (countLit q [-103, -104]) (countLit q [-105, -106]) (count1618 q) 2 (meaning1615 q) (meaning1619 q) hs
  change valuationOf q 1615 = false ∨ valuationOf q 1619 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1277 (q : Snake 81) (h : Conditions q) : valuation q 1615 = false ∨ valuation q 1619 = true := counterClause1277 (baseVal q)

theorem counterClause1278 (q : Nat → Bool) : valuationOf q 1615 = false ∨ valuationOf q 1616 = false ∨ valuationOf q 1620 = true := by
  have hs : count1618 q = (countLit q [-103, -104]) + (countLit q [-105, -106]) := List.countP_append (p := literal q) (l₁ := [-103, -104]) (l₂ := [-105, -106])
  have hm := merge_two (literal (valuationOf q) (1615)) (literal (valuationOf q) (1616)) (literal (valuationOf q) (1620)) (countLit q [-103, -104]) (countLit q [-105, -106]) (count1618 q) 2 1 (meaning1615 q) (meaning1616 q) (meaning1620 q) hs
  change valuationOf q 1615 = false ∨ valuationOf q 1616 = false ∨ valuationOf q 1620 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1278 (q : Snake 81) (h : Conditions q) : valuation q 1615 = false ∨ valuation q 1616 = false ∨ valuation q 1620 = true := counterClause1278 (baseVal q)

theorem counterClause1279 (q : Nat → Bool) : valuationOf q 113 = true ∨ valuationOf q 1622 = true := by
  have hs : count1622 q = (countLit q [-110]) + (countLit q [-113]) := List.countP_append (p := literal q) (l₁ := [-110]) (l₂ := [-113])
  have hm := merge_right (literal (valuationOf q) (-113)) (literal (valuationOf q) (1622)) (countLit q [-110]) (countLit q [-113]) (count1622 q) 1 (meaningNeg113 q) (meaning1622 q) hs
  change (! (valuationOf q 113)) = false ∨ valuationOf q 1622 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1279 (q : Snake 81) (h : Conditions q) : valuation q 113 = true ∨ valuation q 1622 = true := counterClause1279 (baseVal q)

theorem counterClause1280 (q : Nat → Bool) : valuationOf q 110 = true ∨ valuationOf q 1622 = true := by
  have hs : count1622 q = (countLit q [-110]) + (countLit q [-113]) := List.countP_append (p := literal q) (l₁ := [-110]) (l₂ := [-113])
  have hm := merge_left (literal (valuationOf q) (-110)) (literal (valuationOf q) (1622)) (countLit q [-110]) (countLit q [-113]) (count1622 q) 1 (meaningNeg110 q) (meaning1622 q) hs
  change (! (valuationOf q 110)) = false ∨ valuationOf q 1622 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1280 (q : Snake 81) (h : Conditions q) : valuation q 110 = true ∨ valuation q 1622 = true := counterClause1280 (baseVal q)

theorem block39 (q : Snake 81) (h : Conditions q) : B112E064.Block39 (valuation q) :=
  ⟨clause1249 q h, clause1250 q h, clause1251 q h, clause1252 q h, clause1253 q h, clause1254 q h, clause1255 q h, clause1256 q h, clause1257 q h, clause1258 q h, clause1259 q h, clause1260 q h, clause1261 q h, clause1262 q h, clause1263 q h, clause1264 q h, clause1265 q h, clause1266 q h, clause1267 q h, clause1268 q h, clause1269 q h, clause1270 q h, clause1271 q h, clause1272 q h, clause1273 q h, clause1274 q h, clause1275 q h, clause1276 q h, clause1277 q h, clause1278 q h, clause1279 q h, clause1280 q h⟩

end
end Snake9.Regrowth.E112064
