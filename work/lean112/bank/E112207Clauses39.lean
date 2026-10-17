import E112207Semantics
import B112E207Inputs
namespace Snake9.Regrowth.E112207
noncomputable section
local instance blockDec39 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1249 (q : Nat → Bool) : valuationOf q 1598 = false ∨ valuationOf q 1605 = false ∨ valuationOf q 1610 = true := by
  have hs : count1609 q = (countLit q [-90, -92, -93]) + (countLit q [-95, -98, -99, -100]) := List.countP_append (p := literal q) (l₁ := [-90, -92, -93]) (l₂ := [-95, -98, -99, -100])
  have hm := merge_two (literal (valuationOf q) (1598)) (literal (valuationOf q) (1605)) (literal (valuationOf q) (1610)) (countLit q [-90, -92, -93]) (countLit q [-95, -98, -99, -100]) (count1609 q) 1 1 (meaning1598 q) (meaning1605 q) (meaning1610 q) hs
  change valuationOf q 1598 = false ∨ valuationOf q 1605 = false ∨ valuationOf q 1610 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1249 (q : Snake 81) (h : Conditions q) : valuation q 1598 = false ∨ valuation q 1605 = false ∨ valuation q 1610 = true := counterClause1249 (baseVal q)

theorem counterClause1250 (q : Nat → Bool) : valuationOf q 1598 = false ∨ valuationOf q 1606 = false ∨ valuationOf q 1611 = true := by
  have hs : count1609 q = (countLit q [-90, -92, -93]) + (countLit q [-95, -98, -99, -100]) := List.countP_append (p := literal q) (l₁ := [-90, -92, -93]) (l₂ := [-95, -98, -99, -100])
  have hm := merge_two (literal (valuationOf q) (1598)) (literal (valuationOf q) (1606)) (literal (valuationOf q) (1611)) (countLit q [-90, -92, -93]) (countLit q [-95, -98, -99, -100]) (count1609 q) 1 2 (meaning1598 q) (meaning1606 q) (meaning1611 q) hs
  change valuationOf q 1598 = false ∨ valuationOf q 1606 = false ∨ valuationOf q 1611 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1250 (q : Snake 81) (h : Conditions q) : valuation q 1598 = false ∨ valuation q 1606 = false ∨ valuation q 1611 = true := counterClause1250 (baseVal q)

theorem counterClause1251 (q : Nat → Bool) : valuationOf q 1599 = false ∨ valuationOf q 1610 = true := by
  have hs : count1609 q = (countLit q [-90, -92, -93]) + (countLit q [-95, -98, -99, -100]) := List.countP_append (p := literal q) (l₁ := [-90, -92, -93]) (l₂ := [-95, -98, -99, -100])
  have hm := merge_left (literal (valuationOf q) (1599)) (literal (valuationOf q) (1610)) (countLit q [-90, -92, -93]) (countLit q [-95, -98, -99, -100]) (count1609 q) 2 (meaning1599 q) (meaning1610 q) hs
  change valuationOf q 1599 = false ∨ valuationOf q 1610 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1251 (q : Snake 81) (h : Conditions q) : valuation q 1599 = false ∨ valuation q 1610 = true := counterClause1251 (baseVal q)

theorem counterClause1252 (q : Nat → Bool) : valuationOf q 1599 = false ∨ valuationOf q 1605 = false ∨ valuationOf q 1611 = true := by
  have hs : count1609 q = (countLit q [-90, -92, -93]) + (countLit q [-95, -98, -99, -100]) := List.countP_append (p := literal q) (l₁ := [-90, -92, -93]) (l₂ := [-95, -98, -99, -100])
  have hm := merge_two (literal (valuationOf q) (1599)) (literal (valuationOf q) (1605)) (literal (valuationOf q) (1611)) (countLit q [-90, -92, -93]) (countLit q [-95, -98, -99, -100]) (count1609 q) 2 1 (meaning1599 q) (meaning1605 q) (meaning1611 q) hs
  change valuationOf q 1599 = false ∨ valuationOf q 1605 = false ∨ valuationOf q 1611 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1252 (q : Snake 81) (h : Conditions q) : valuation q 1599 = false ∨ valuation q 1605 = false ∨ valuation q 1611 = true := counterClause1252 (baseVal q)

theorem counterClause1253 (q : Nat → Bool) : valuationOf q 1599 = false ∨ valuationOf q 1606 = false ∨ valuationOf q 1612 = true := by
  have hs : count1609 q = (countLit q [-90, -92, -93]) + (countLit q [-95, -98, -99, -100]) := List.countP_append (p := literal q) (l₁ := [-90, -92, -93]) (l₂ := [-95, -98, -99, -100])
  have hm := merge_two (literal (valuationOf q) (1599)) (literal (valuationOf q) (1606)) (literal (valuationOf q) (1612)) (countLit q [-90, -92, -93]) (countLit q [-95, -98, -99, -100]) (count1609 q) 2 2 (meaning1599 q) (meaning1606 q) (meaning1612 q) hs
  change valuationOf q 1599 = false ∨ valuationOf q 1606 = false ∨ valuationOf q 1612 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1253 (q : Snake 81) (h : Conditions q) : valuation q 1599 = false ∨ valuation q 1606 = false ∨ valuation q 1612 = true := counterClause1253 (baseVal q)

theorem counterClause1254 (q : Nat → Bool) : valuationOf q 1599 = false ∨ valuationOf q 1607 = false ∨ valuationOf q 1613 = true := by
  have hs : count1609 q = (countLit q [-90, -92, -93]) + (countLit q [-95, -98, -99, -100]) := List.countP_append (p := literal q) (l₁ := [-90, -92, -93]) (l₂ := [-95, -98, -99, -100])
  have hm := merge_two (literal (valuationOf q) (1599)) (literal (valuationOf q) (1607)) (literal (valuationOf q) (1613)) (countLit q [-90, -92, -93]) (countLit q [-95, -98, -99, -100]) (count1609 q) 2 3 (meaning1599 q) (meaning1607 q) (meaning1613 q) hs
  change valuationOf q 1599 = false ∨ valuationOf q 1607 = false ∨ valuationOf q 1613 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1254 (q : Snake 81) (h : Conditions q) : valuation q 1599 = false ∨ valuation q 1607 = false ∨ valuation q 1613 = true := counterClause1254 (baseVal q)

theorem counterClause1255 (q : Nat → Bool) : valuationOf q 1600 = false ∨ valuationOf q 1611 = true := by
  have hs : count1609 q = (countLit q [-90, -92, -93]) + (countLit q [-95, -98, -99, -100]) := List.countP_append (p := literal q) (l₁ := [-90, -92, -93]) (l₂ := [-95, -98, -99, -100])
  have hm := merge_left (literal (valuationOf q) (1600)) (literal (valuationOf q) (1611)) (countLit q [-90, -92, -93]) (countLit q [-95, -98, -99, -100]) (count1609 q) 3 (meaning1600 q) (meaning1611 q) hs
  change valuationOf q 1600 = false ∨ valuationOf q 1611 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1255 (q : Snake 81) (h : Conditions q) : valuation q 1600 = false ∨ valuation q 1611 = true := counterClause1255 (baseVal q)

theorem counterClause1256 (q : Nat → Bool) : valuationOf q 1600 = false ∨ valuationOf q 1605 = false ∨ valuationOf q 1612 = true := by
  have hs : count1609 q = (countLit q [-90, -92, -93]) + (countLit q [-95, -98, -99, -100]) := List.countP_append (p := literal q) (l₁ := [-90, -92, -93]) (l₂ := [-95, -98, -99, -100])
  have hm := merge_two (literal (valuationOf q) (1600)) (literal (valuationOf q) (1605)) (literal (valuationOf q) (1612)) (countLit q [-90, -92, -93]) (countLit q [-95, -98, -99, -100]) (count1609 q) 3 1 (meaning1600 q) (meaning1605 q) (meaning1612 q) hs
  change valuationOf q 1600 = false ∨ valuationOf q 1605 = false ∨ valuationOf q 1612 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1256 (q : Snake 81) (h : Conditions q) : valuation q 1600 = false ∨ valuation q 1605 = false ∨ valuation q 1612 = true := counterClause1256 (baseVal q)

theorem counterClause1257 (q : Nat → Bool) : valuationOf q 1600 = false ∨ valuationOf q 1606 = false ∨ valuationOf q 1613 = true := by
  have hs : count1609 q = (countLit q [-90, -92, -93]) + (countLit q [-95, -98, -99, -100]) := List.countP_append (p := literal q) (l₁ := [-90, -92, -93]) (l₂ := [-95, -98, -99, -100])
  have hm := merge_two (literal (valuationOf q) (1600)) (literal (valuationOf q) (1606)) (literal (valuationOf q) (1613)) (countLit q [-90, -92, -93]) (countLit q [-95, -98, -99, -100]) (count1609 q) 3 2 (meaning1600 q) (meaning1606 q) (meaning1613 q) hs
  change valuationOf q 1600 = false ∨ valuationOf q 1606 = false ∨ valuationOf q 1613 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1257 (q : Snake 81) (h : Conditions q) : valuation q 1600 = false ∨ valuation q 1606 = false ∨ valuation q 1613 = true := counterClause1257 (baseVal q)

theorem counterClause1258 (q : Nat → Bool) : valuationOf q 101 = true ∨ valuationOf q 1616 = true := by
  have hs : count1616 q = (countLit q [-101]) + (countLit q [-105]) := List.countP_append (p := literal q) (l₁ := [-101]) (l₂ := [-105])
  have hm := merge_left (literal (valuationOf q) (-101)) (literal (valuationOf q) (1616)) (countLit q [-101]) (countLit q [-105]) (count1616 q) 1 (meaningNeg101 q) (meaning1616 q) hs
  change (! (valuationOf q 101)) = false ∨ valuationOf q 1616 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1258 (q : Snake 81) (h : Conditions q) : valuation q 101 = true ∨ valuation q 1616 = true := counterClause1258 (baseVal q)

theorem counterClause1259 (q : Nat → Bool) : valuationOf q 1616 = false ∨ valuationOf q 1620 = true := by
  have hs : count1620 q = (countLit q [-101, -105]) + (countLit q [-107, -108]) := List.countP_append (p := literal q) (l₁ := [-101, -105]) (l₂ := [-107, -108])
  have hm := merge_left (literal (valuationOf q) (1616)) (literal (valuationOf q) (1620)) (countLit q [-101, -105]) (countLit q [-107, -108]) (count1620 q) 1 (meaning1616 q) (meaning1620 q) hs
  change valuationOf q 1616 = false ∨ valuationOf q 1620 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1259 (q : Snake 81) (h : Conditions q) : valuation q 1616 = false ∨ valuation q 1620 = true := counterClause1259 (baseVal q)

theorem counterClause1260 (q : Nat → Bool) : valuationOf q 113 = true ∨ valuationOf q 1624 = true := by
  have hs : count1624 q = (countLit q [-112]) + (countLit q [-113]) := List.countP_append (p := literal q) (l₁ := [-112]) (l₂ := [-113])
  have hm := merge_right (literal (valuationOf q) (-113)) (literal (valuationOf q) (1624)) (countLit q [-112]) (countLit q [-113]) (count1624 q) 1 (meaningNeg113 q) (meaning1624 q) hs
  change (! (valuationOf q 113)) = false ∨ valuationOf q 1624 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1260 (q : Snake 81) (h : Conditions q) : valuation q 113 = true ∨ valuation q 1624 = true := counterClause1260 (baseVal q)

theorem counterClause1261 (q : Nat → Bool) : valuationOf q 112 = true ∨ valuationOf q 1624 = true := by
  have hs : count1624 q = (countLit q [-112]) + (countLit q [-113]) := List.countP_append (p := literal q) (l₁ := [-112]) (l₂ := [-113])
  have hm := merge_left (literal (valuationOf q) (-112)) (literal (valuationOf q) (1624)) (countLit q [-112]) (countLit q [-113]) (count1624 q) 1 (meaningNeg112 q) (meaning1624 q) hs
  change (! (valuationOf q 112)) = false ∨ valuationOf q 1624 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1261 (q : Snake 81) (h : Conditions q) : valuation q 112 = true ∨ valuation q 1624 = true := counterClause1261 (baseVal q)

theorem counterClause1262 (q : Nat → Bool) : valuationOf q 115 = true ∨ valuationOf q 1626 = true := by
  have hs : count1626 q = (countLit q [-114]) + (countLit q [-115]) := List.countP_append (p := literal q) (l₁ := [-114]) (l₂ := [-115])
  have hm := merge_right (literal (valuationOf q) (-115)) (literal (valuationOf q) (1626)) (countLit q [-114]) (countLit q [-115]) (count1626 q) 1 (meaningNeg115 q) (meaning1626 q) hs
  change (! (valuationOf q 115)) = false ∨ valuationOf q 1626 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1262 (q : Snake 81) (h : Conditions q) : valuation q 115 = true ∨ valuation q 1626 = true := counterClause1262 (baseVal q)

theorem counterClause1263 (q : Nat → Bool) : valuationOf q 114 = true ∨ valuationOf q 1626 = true := by
  have hs : count1626 q = (countLit q [-114]) + (countLit q [-115]) := List.countP_append (p := literal q) (l₁ := [-114]) (l₂ := [-115])
  have hm := merge_left (literal (valuationOf q) (-114)) (literal (valuationOf q) (1626)) (countLit q [-114]) (countLit q [-115]) (count1626 q) 1 (meaningNeg114 q) (meaning1626 q) hs
  change (! (valuationOf q 114)) = false ∨ valuationOf q 1626 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1263 (q : Snake 81) (h : Conditions q) : valuation q 114 = true ∨ valuation q 1626 = true := counterClause1263 (baseVal q)

theorem counterClause1264 (q : Nat → Bool) : valuationOf q 1626 = false ∨ valuationOf q 1628 = true := by
  have hs : count1628 q = (countLit q [-112, -113]) + (countLit q [-114, -115]) := List.countP_append (p := literal q) (l₁ := [-112, -113]) (l₂ := [-114, -115])
  have hm := merge_right (literal (valuationOf q) (1626)) (literal (valuationOf q) (1628)) (countLit q [-112, -113]) (countLit q [-114, -115]) (count1628 q) 1 (meaning1626 q) (meaning1628 q) hs
  change valuationOf q 1626 = false ∨ valuationOf q 1628 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1264 (q : Snake 81) (h : Conditions q) : valuation q 1626 = false ∨ valuation q 1628 = true := counterClause1264 (baseVal q)

theorem counterClause1265 (q : Nat → Bool) : valuationOf q 1624 = false ∨ valuationOf q 1628 = true := by
  have hs : count1628 q = (countLit q [-112, -113]) + (countLit q [-114, -115]) := List.countP_append (p := literal q) (l₁ := [-112, -113]) (l₂ := [-114, -115])
  have hm := merge_left (literal (valuationOf q) (1624)) (literal (valuationOf q) (1628)) (countLit q [-112, -113]) (countLit q [-114, -115]) (count1628 q) 1 (meaning1624 q) (meaning1628 q) hs
  change valuationOf q 1624 = false ∨ valuationOf q 1628 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1265 (q : Snake 81) (h : Conditions q) : valuation q 1624 = false ∨ valuation q 1628 = true := counterClause1265 (baseVal q)

theorem counterClause1266 (q : Nat → Bool) : valuationOf q 1628 = false ∨ valuationOf q 1632 = true := by
  have hs : count1632 q = (countLit q [-101, -105, -107, -108]) + (countLit q [-112, -113, -114, -115]) := List.countP_append (p := literal q) (l₁ := [-101, -105, -107, -108]) (l₂ := [-112, -113, -114, -115])
  have hm := merge_right (literal (valuationOf q) (1628)) (literal (valuationOf q) (1632)) (countLit q [-101, -105, -107, -108]) (countLit q [-112, -113, -114, -115]) (count1632 q) 1 (meaning1628 q) (meaning1632 q) hs
  change valuationOf q 1628 = false ∨ valuationOf q 1632 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1266 (q : Snake 81) (h : Conditions q) : valuation q 1628 = false ∨ valuation q 1632 = true := counterClause1266 (baseVal q)

theorem counterClause1267 (q : Nat → Bool) : valuationOf q 1620 = false ∨ valuationOf q 1628 = false ∨ valuationOf q 1633 = true := by
  have hs : count1632 q = (countLit q [-101, -105, -107, -108]) + (countLit q [-112, -113, -114, -115]) := List.countP_append (p := literal q) (l₁ := [-101, -105, -107, -108]) (l₂ := [-112, -113, -114, -115])
  have hm := merge_two (literal (valuationOf q) (1620)) (literal (valuationOf q) (1628)) (literal (valuationOf q) (1633)) (countLit q [-101, -105, -107, -108]) (countLit q [-112, -113, -114, -115]) (count1632 q) 1 1 (meaning1620 q) (meaning1628 q) (meaning1633 q) hs
  change valuationOf q 1620 = false ∨ valuationOf q 1628 = false ∨ valuationOf q 1633 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1267 (q : Snake 81) (h : Conditions q) : valuation q 1620 = false ∨ valuation q 1628 = false ∨ valuation q 1633 = true := counterClause1267 (baseVal q)

theorem counterClause1268 (q : Nat → Bool) : valuationOf q 1632 = false ∨ valuationOf q 1640 = true := by
  have hs : count1640 q = (countLit q [-90, -92, -93, -95, -98, -99, -100]) + (countLit q [-101, -105, -107, -108, -112, -113, -114, -115]) := List.countP_append (p := literal q) (l₁ := [-90, -92, -93, -95, -98, -99, -100]) (l₂ := [-101, -105, -107, -108, -112, -113, -114, -115])
  have hm := merge_right (literal (valuationOf q) (1632)) (literal (valuationOf q) (1640)) (countLit q [-90, -92, -93, -95, -98, -99, -100]) (countLit q [-101, -105, -107, -108, -112, -113, -114, -115]) (count1640 q) 1 (meaning1632 q) (meaning1640 q) hs
  change valuationOf q 1632 = false ∨ valuationOf q 1640 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1268 (q : Snake 81) (h : Conditions q) : valuation q 1632 = false ∨ valuation q 1640 = true := counterClause1268 (baseVal q)

theorem counterClause1269 (q : Nat → Bool) : valuationOf q 1633 = false ∨ valuationOf q 1641 = true := by
  have hs : count1640 q = (countLit q [-90, -92, -93, -95, -98, -99, -100]) + (countLit q [-101, -105, -107, -108, -112, -113, -114, -115]) := List.countP_append (p := literal q) (l₁ := [-90, -92, -93, -95, -98, -99, -100]) (l₂ := [-101, -105, -107, -108, -112, -113, -114, -115])
  have hm := merge_right (literal (valuationOf q) (1633)) (literal (valuationOf q) (1641)) (countLit q [-90, -92, -93, -95, -98, -99, -100]) (countLit q [-101, -105, -107, -108, -112, -113, -114, -115]) (count1640 q) 2 (meaning1633 q) (meaning1641 q) hs
  change valuationOf q 1633 = false ∨ valuationOf q 1641 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1269 (q : Snake 81) (h : Conditions q) : valuation q 1633 = false ∨ valuation q 1641 = true := counterClause1269 (baseVal q)

theorem counterClause1270 (q : Nat → Bool) : valuationOf q 1609 = false ∨ valuationOf q 1632 = false ∨ valuationOf q 1641 = true := by
  have hs : count1640 q = (countLit q [-90, -92, -93, -95, -98, -99, -100]) + (countLit q [-101, -105, -107, -108, -112, -113, -114, -115]) := List.countP_append (p := literal q) (l₁ := [-90, -92, -93, -95, -98, -99, -100]) (l₂ := [-101, -105, -107, -108, -112, -113, -114, -115])
  have hm := merge_two (literal (valuationOf q) (1609)) (literal (valuationOf q) (1632)) (literal (valuationOf q) (1641)) (countLit q [-90, -92, -93, -95, -98, -99, -100]) (countLit q [-101, -105, -107, -108, -112, -113, -114, -115]) (count1640 q) 1 1 (meaning1609 q) (meaning1632 q) (meaning1641 q) hs
  change valuationOf q 1609 = false ∨ valuationOf q 1632 = false ∨ valuationOf q 1641 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1270 (q : Snake 81) (h : Conditions q) : valuation q 1609 = false ∨ valuation q 1632 = false ∨ valuation q 1641 = true := counterClause1270 (baseVal q)

theorem counterClause1271 (q : Nat → Bool) : valuationOf q 1609 = false ∨ valuationOf q 1633 = false ∨ valuationOf q 1642 = true := by
  have hs : count1640 q = (countLit q [-90, -92, -93, -95, -98, -99, -100]) + (countLit q [-101, -105, -107, -108, -112, -113, -114, -115]) := List.countP_append (p := literal q) (l₁ := [-90, -92, -93, -95, -98, -99, -100]) (l₂ := [-101, -105, -107, -108, -112, -113, -114, -115])
  have hm := merge_two (literal (valuationOf q) (1609)) (literal (valuationOf q) (1633)) (literal (valuationOf q) (1642)) (countLit q [-90, -92, -93, -95, -98, -99, -100]) (countLit q [-101, -105, -107, -108, -112, -113, -114, -115]) (count1640 q) 1 2 (meaning1609 q) (meaning1633 q) (meaning1642 q) hs
  change valuationOf q 1609 = false ∨ valuationOf q 1633 = false ∨ valuationOf q 1642 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1271 (q : Snake 81) (h : Conditions q) : valuation q 1609 = false ∨ valuation q 1633 = false ∨ valuation q 1642 = true := counterClause1271 (baseVal q)

theorem counterClause1272 (q : Nat → Bool) : valuationOf q 1610 = false ∨ valuationOf q 1632 = false ∨ valuationOf q 1642 = true := by
  have hs : count1640 q = (countLit q [-90, -92, -93, -95, -98, -99, -100]) + (countLit q [-101, -105, -107, -108, -112, -113, -114, -115]) := List.countP_append (p := literal q) (l₁ := [-90, -92, -93, -95, -98, -99, -100]) (l₂ := [-101, -105, -107, -108, -112, -113, -114, -115])
  have hm := merge_two (literal (valuationOf q) (1610)) (literal (valuationOf q) (1632)) (literal (valuationOf q) (1642)) (countLit q [-90, -92, -93, -95, -98, -99, -100]) (countLit q [-101, -105, -107, -108, -112, -113, -114, -115]) (count1640 q) 2 1 (meaning1610 q) (meaning1632 q) (meaning1642 q) hs
  change valuationOf q 1610 = false ∨ valuationOf q 1632 = false ∨ valuationOf q 1642 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1272 (q : Snake 81) (h : Conditions q) : valuation q 1610 = false ∨ valuation q 1632 = false ∨ valuation q 1642 = true := counterClause1272 (baseVal q)

theorem counterClause1273 (q : Nat → Bool) : valuationOf q 1610 = false ∨ valuationOf q 1633 = false ∨ valuationOf q 1643 = true := by
  have hs : count1640 q = (countLit q [-90, -92, -93, -95, -98, -99, -100]) + (countLit q [-101, -105, -107, -108, -112, -113, -114, -115]) := List.countP_append (p := literal q) (l₁ := [-90, -92, -93, -95, -98, -99, -100]) (l₂ := [-101, -105, -107, -108, -112, -113, -114, -115])
  have hm := merge_two (literal (valuationOf q) (1610)) (literal (valuationOf q) (1633)) (literal (valuationOf q) (1643)) (countLit q [-90, -92, -93, -95, -98, -99, -100]) (countLit q [-101, -105, -107, -108, -112, -113, -114, -115]) (count1640 q) 2 2 (meaning1610 q) (meaning1633 q) (meaning1643 q) hs
  change valuationOf q 1610 = false ∨ valuationOf q 1633 = false ∨ valuationOf q 1643 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1273 (q : Snake 81) (h : Conditions q) : valuation q 1610 = false ∨ valuation q 1633 = false ∨ valuation q 1643 = true := counterClause1273 (baseVal q)

theorem counterClause1274 (q : Nat → Bool) : valuationOf q 1611 = false ∨ valuationOf q 1632 = false ∨ valuationOf q 1643 = true := by
  have hs : count1640 q = (countLit q [-90, -92, -93, -95, -98, -99, -100]) + (countLit q [-101, -105, -107, -108, -112, -113, -114, -115]) := List.countP_append (p := literal q) (l₁ := [-90, -92, -93, -95, -98, -99, -100]) (l₂ := [-101, -105, -107, -108, -112, -113, -114, -115])
  have hm := merge_two (literal (valuationOf q) (1611)) (literal (valuationOf q) (1632)) (literal (valuationOf q) (1643)) (countLit q [-90, -92, -93, -95, -98, -99, -100]) (countLit q [-101, -105, -107, -108, -112, -113, -114, -115]) (count1640 q) 3 1 (meaning1611 q) (meaning1632 q) (meaning1643 q) hs
  change valuationOf q 1611 = false ∨ valuationOf q 1632 = false ∨ valuationOf q 1643 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1274 (q : Snake 81) (h : Conditions q) : valuation q 1611 = false ∨ valuation q 1632 = false ∨ valuation q 1643 = true := counterClause1274 (baseVal q)

theorem counterClause1275 (q : Nat → Bool) : valuationOf q 1611 = false ∨ valuationOf q 1633 = false ∨ valuationOf q 1644 = true := by
  have hs : count1640 q = (countLit q [-90, -92, -93, -95, -98, -99, -100]) + (countLit q [-101, -105, -107, -108, -112, -113, -114, -115]) := List.countP_append (p := literal q) (l₁ := [-90, -92, -93, -95, -98, -99, -100]) (l₂ := [-101, -105, -107, -108, -112, -113, -114, -115])
  have hm := merge_two (literal (valuationOf q) (1611)) (literal (valuationOf q) (1633)) (literal (valuationOf q) (1644)) (countLit q [-90, -92, -93, -95, -98, -99, -100]) (countLit q [-101, -105, -107, -108, -112, -113, -114, -115]) (count1640 q) 3 2 (meaning1611 q) (meaning1633 q) (meaning1644 q) hs
  change valuationOf q 1611 = false ∨ valuationOf q 1633 = false ∨ valuationOf q 1644 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1275 (q : Snake 81) (h : Conditions q) : valuation q 1611 = false ∨ valuation q 1633 = false ∨ valuation q 1644 = true := counterClause1275 (baseVal q)

theorem counterClause1276 (q : Nat → Bool) : valuationOf q 1612 = false ∨ valuationOf q 1632 = false ∨ valuationOf q 1644 = true := by
  have hs : count1640 q = (countLit q [-90, -92, -93, -95, -98, -99, -100]) + (countLit q [-101, -105, -107, -108, -112, -113, -114, -115]) := List.countP_append (p := literal q) (l₁ := [-90, -92, -93, -95, -98, -99, -100]) (l₂ := [-101, -105, -107, -108, -112, -113, -114, -115])
  have hm := merge_two (literal (valuationOf q) (1612)) (literal (valuationOf q) (1632)) (literal (valuationOf q) (1644)) (countLit q [-90, -92, -93, -95, -98, -99, -100]) (countLit q [-101, -105, -107, -108, -112, -113, -114, -115]) (count1640 q) 4 1 (meaning1612 q) (meaning1632 q) (meaning1644 q) hs
  change valuationOf q 1612 = false ∨ valuationOf q 1632 = false ∨ valuationOf q 1644 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1276 (q : Snake 81) (h : Conditions q) : valuation q 1612 = false ∨ valuation q 1632 = false ∨ valuation q 1644 = true := counterClause1276 (baseVal q)

theorem counterClause1277 (q : Nat → Bool) : valuationOf q 1612 = false ∨ valuationOf q 1633 = false ∨ valuationOf q 1645 = true := by
  have hs : count1640 q = (countLit q [-90, -92, -93, -95, -98, -99, -100]) + (countLit q [-101, -105, -107, -108, -112, -113, -114, -115]) := List.countP_append (p := literal q) (l₁ := [-90, -92, -93, -95, -98, -99, -100]) (l₂ := [-101, -105, -107, -108, -112, -113, -114, -115])
  have hm := merge_two (literal (valuationOf q) (1612)) (literal (valuationOf q) (1633)) (literal (valuationOf q) (1645)) (countLit q [-90, -92, -93, -95, -98, -99, -100]) (countLit q [-101, -105, -107, -108, -112, -113, -114, -115]) (count1640 q) 4 2 (meaning1612 q) (meaning1633 q) (meaning1645 q) hs
  change valuationOf q 1612 = false ∨ valuationOf q 1633 = false ∨ valuationOf q 1645 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1277 (q : Snake 81) (h : Conditions q) : valuation q 1612 = false ∨ valuation q 1633 = false ∨ valuation q 1645 = true := counterClause1277 (baseVal q)

theorem counterClause1278 (q : Nat → Bool) : valuationOf q 1613 = false ∨ valuationOf q 1632 = false ∨ valuationOf q 1645 = true := by
  have hs : count1640 q = (countLit q [-90, -92, -93, -95, -98, -99, -100]) + (countLit q [-101, -105, -107, -108, -112, -113, -114, -115]) := List.countP_append (p := literal q) (l₁ := [-90, -92, -93, -95, -98, -99, -100]) (l₂ := [-101, -105, -107, -108, -112, -113, -114, -115])
  have hm := merge_two (literal (valuationOf q) (1613)) (literal (valuationOf q) (1632)) (literal (valuationOf q) (1645)) (countLit q [-90, -92, -93, -95, -98, -99, -100]) (countLit q [-101, -105, -107, -108, -112, -113, -114, -115]) (count1640 q) 5 1 (meaning1613 q) (meaning1632 q) (meaning1645 q) hs
  change valuationOf q 1613 = false ∨ valuationOf q 1632 = false ∨ valuationOf q 1645 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1278 (q : Snake 81) (h : Conditions q) : valuation q 1613 = false ∨ valuation q 1632 = false ∨ valuation q 1645 = true := counterClause1278 (baseVal q)

theorem counterClause1279 (q : Nat → Bool) : valuationOf q 1583 = false ∨ valuationOf q 1642 = false ∨ valuationOf q 1659 = true := by
  have hs : count1655 q = (countLit q [-62, -63, -66, -69, -71, -72, -74, -75, -79, -80, -81, -82, -86, -89]) + (countLit q [-90, -92, -93, -95, -98, -99, -100, -101, -105, -107, -108, -112, -113, -114, -115]) := List.countP_append (p := literal q) (l₁ := [-62, -63, -66, -69, -71, -72, -74, -75, -79, -80, -81, -82, -86, -89]) (l₂ := [-90, -92, -93, -95, -98, -99, -100, -101, -105, -107, -108, -112, -113, -114, -115])
  have hm := merge_two (literal (valuationOf q) (1583)) (literal (valuationOf q) (1642)) (literal (valuationOf q) (1659)) (countLit q [-62, -63, -66, -69, -71, -72, -74, -75, -79, -80, -81, -82, -86, -89]) (countLit q [-90, -92, -93, -95, -98, -99, -100, -101, -105, -107, -108, -112, -113, -114, -115]) (count1655 q) 2 3 (meaning1583 q) (meaning1642 q) (meaning1659 q) hs
  change valuationOf q 1583 = false ∨ valuationOf q 1642 = false ∨ valuationOf q 1659 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1279 (q : Snake 81) (h : Conditions q) : valuation q 1583 = false ∨ valuation q 1642 = false ∨ valuation q 1659 = true := counterClause1279 (baseVal q)

theorem counterClause1280 (q : Nat → Bool) : valuationOf q 1583 = false ∨ valuationOf q 1643 = false ∨ valuationOf q 1660 = true := by
  have hs : count1655 q = (countLit q [-62, -63, -66, -69, -71, -72, -74, -75, -79, -80, -81, -82, -86, -89]) + (countLit q [-90, -92, -93, -95, -98, -99, -100, -101, -105, -107, -108, -112, -113, -114, -115]) := List.countP_append (p := literal q) (l₁ := [-62, -63, -66, -69, -71, -72, -74, -75, -79, -80, -81, -82, -86, -89]) (l₂ := [-90, -92, -93, -95, -98, -99, -100, -101, -105, -107, -108, -112, -113, -114, -115])
  have hm := merge_two (literal (valuationOf q) (1583)) (literal (valuationOf q) (1643)) (literal (valuationOf q) (1660)) (countLit q [-62, -63, -66, -69, -71, -72, -74, -75, -79, -80, -81, -82, -86, -89]) (countLit q [-90, -92, -93, -95, -98, -99, -100, -101, -105, -107, -108, -112, -113, -114, -115]) (count1655 q) 2 4 (meaning1583 q) (meaning1643 q) (meaning1660 q) hs
  change valuationOf q 1583 = false ∨ valuationOf q 1643 = false ∨ valuationOf q 1660 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1280 (q : Snake 81) (h : Conditions q) : valuation q 1583 = false ∨ valuation q 1643 = false ∨ valuation q 1660 = true := counterClause1280 (baseVal q)

theorem block39 (q : Snake 81) (h : Conditions q) : B112E207.Block39 (valuation q) :=
  ⟨clause1249 q h, clause1250 q h, clause1251 q h, clause1252 q h, clause1253 q h, clause1254 q h, clause1255 q h, clause1256 q h, clause1257 q h, clause1258 q h, clause1259 q h, clause1260 q h, clause1261 q h, clause1262 q h, clause1263 q h, clause1264 q h, clause1265 q h, clause1266 q h, clause1267 q h, clause1268 q h, clause1269 q h, clause1270 q h, clause1271 q h, clause1272 q h, clause1273 q h, clause1274 q h, clause1275 q h, clause1276 q h, clause1277 q h, clause1278 q h, clause1279 q h, clause1280 q h⟩

end
end Snake9.Regrowth.E112207
