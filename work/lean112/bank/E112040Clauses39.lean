import E112040Semantics
import B112E040Inputs
namespace Snake9.Regrowth.E112040
noncomputable section
local instance blockDec39 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1249 (q : Nat → Bool) : valuationOf q 1589 = false ∨ valuationOf q 1593 = true := by
  have hs : count1593 q = (countLit q [-61, -62, -63]) + (countLit q [-64, -70, -71, -73]) := List.countP_append (p := literal q) (l₁ := [-61, -62, -63]) (l₂ := [-64, -70, -71, -73])
  have hm := merge_right (literal (valuationOf q) (1589)) (literal (valuationOf q) (1593)) (countLit q [-61, -62, -63]) (countLit q [-64, -70, -71, -73]) (count1593 q) 1 (meaning1589 q) (meaning1593 q) hs
  change valuationOf q 1589 = false ∨ valuationOf q 1593 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1249 (q : Snake 81) (h : Conditions q) : valuation q 1589 = false ∨ valuation q 1593 = true := counterClause1249 (baseVal q)

theorem counterClause1250 (q : Nat → Bool) : valuationOf q 1590 = false ∨ valuationOf q 1594 = true := by
  have hs : count1593 q = (countLit q [-61, -62, -63]) + (countLit q [-64, -70, -71, -73]) := List.countP_append (p := literal q) (l₁ := [-61, -62, -63]) (l₂ := [-64, -70, -71, -73])
  have hm := merge_right (literal (valuationOf q) (1590)) (literal (valuationOf q) (1594)) (countLit q [-61, -62, -63]) (countLit q [-64, -70, -71, -73]) (count1593 q) 2 (meaning1590 q) (meaning1594 q) hs
  change valuationOf q 1590 = false ∨ valuationOf q 1594 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1250 (q : Snake 81) (h : Conditions q) : valuation q 1590 = false ∨ valuation q 1594 = true := counterClause1250 (baseVal q)

theorem counterClause1251 (q : Nat → Bool) : valuationOf q 1591 = false ∨ valuationOf q 1595 = true := by
  have hs : count1593 q = (countLit q [-61, -62, -63]) + (countLit q [-64, -70, -71, -73]) := List.countP_append (p := literal q) (l₁ := [-61, -62, -63]) (l₂ := [-64, -70, -71, -73])
  have hm := merge_right (literal (valuationOf q) (1591)) (literal (valuationOf q) (1595)) (countLit q [-61, -62, -63]) (countLit q [-64, -70, -71, -73]) (count1593 q) 3 (meaning1591 q) (meaning1595 q) hs
  change valuationOf q 1591 = false ∨ valuationOf q 1595 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1251 (q : Snake 81) (h : Conditions q) : valuation q 1591 = false ∨ valuation q 1595 = true := counterClause1251 (baseVal q)

theorem counterClause1252 (q : Nat → Bool) : valuationOf q 1582 = false ∨ valuationOf q 1593 = true := by
  have hs : count1593 q = (countLit q [-61, -62, -63]) + (countLit q [-64, -70, -71, -73]) := List.countP_append (p := literal q) (l₁ := [-61, -62, -63]) (l₂ := [-64, -70, -71, -73])
  have hm := merge_left (literal (valuationOf q) (1582)) (literal (valuationOf q) (1593)) (countLit q [-61, -62, -63]) (countLit q [-64, -70, -71, -73]) (count1593 q) 1 (meaning1582 q) (meaning1593 q) hs
  change valuationOf q 1582 = false ∨ valuationOf q 1593 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1252 (q : Snake 81) (h : Conditions q) : valuation q 1582 = false ∨ valuation q 1593 = true := counterClause1252 (baseVal q)

theorem counterClause1253 (q : Nat → Bool) : valuationOf q 1582 = false ∨ valuationOf q 1589 = false ∨ valuationOf q 1594 = true := by
  have hs : count1593 q = (countLit q [-61, -62, -63]) + (countLit q [-64, -70, -71, -73]) := List.countP_append (p := literal q) (l₁ := [-61, -62, -63]) (l₂ := [-64, -70, -71, -73])
  have hm := merge_two (literal (valuationOf q) (1582)) (literal (valuationOf q) (1589)) (literal (valuationOf q) (1594)) (countLit q [-61, -62, -63]) (countLit q [-64, -70, -71, -73]) (count1593 q) 1 1 (meaning1582 q) (meaning1589 q) (meaning1594 q) hs
  change valuationOf q 1582 = false ∨ valuationOf q 1589 = false ∨ valuationOf q 1594 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1253 (q : Snake 81) (h : Conditions q) : valuation q 1582 = false ∨ valuation q 1589 = false ∨ valuation q 1594 = true := counterClause1253 (baseVal q)

theorem counterClause1254 (q : Nat → Bool) : valuationOf q 1582 = false ∨ valuationOf q 1590 = false ∨ valuationOf q 1595 = true := by
  have hs : count1593 q = (countLit q [-61, -62, -63]) + (countLit q [-64, -70, -71, -73]) := List.countP_append (p := literal q) (l₁ := [-61, -62, -63]) (l₂ := [-64, -70, -71, -73])
  have hm := merge_two (literal (valuationOf q) (1582)) (literal (valuationOf q) (1590)) (literal (valuationOf q) (1595)) (countLit q [-61, -62, -63]) (countLit q [-64, -70, -71, -73]) (count1593 q) 1 2 (meaning1582 q) (meaning1590 q) (meaning1595 q) hs
  change valuationOf q 1582 = false ∨ valuationOf q 1590 = false ∨ valuationOf q 1595 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1254 (q : Snake 81) (h : Conditions q) : valuation q 1582 = false ∨ valuation q 1590 = false ∨ valuation q 1595 = true := counterClause1254 (baseVal q)

theorem counterClause1255 (q : Nat → Bool) : valuationOf q 1582 = false ∨ valuationOf q 1591 = false ∨ valuationOf q 1596 = true := by
  have hs : count1593 q = (countLit q [-61, -62, -63]) + (countLit q [-64, -70, -71, -73]) := List.countP_append (p := literal q) (l₁ := [-61, -62, -63]) (l₂ := [-64, -70, -71, -73])
  have hm := merge_two (literal (valuationOf q) (1582)) (literal (valuationOf q) (1591)) (literal (valuationOf q) (1596)) (countLit q [-61, -62, -63]) (countLit q [-64, -70, -71, -73]) (count1593 q) 1 3 (meaning1582 q) (meaning1591 q) (meaning1596 q) hs
  change valuationOf q 1582 = false ∨ valuationOf q 1591 = false ∨ valuationOf q 1596 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1255 (q : Snake 81) (h : Conditions q) : valuation q 1582 = false ∨ valuation q 1591 = false ∨ valuation q 1596 = true := counterClause1255 (baseVal q)

theorem counterClause1256 (q : Nat → Bool) : valuationOf q 1583 = false ∨ valuationOf q 1594 = true := by
  have hs : count1593 q = (countLit q [-61, -62, -63]) + (countLit q [-64, -70, -71, -73]) := List.countP_append (p := literal q) (l₁ := [-61, -62, -63]) (l₂ := [-64, -70, -71, -73])
  have hm := merge_left (literal (valuationOf q) (1583)) (literal (valuationOf q) (1594)) (countLit q [-61, -62, -63]) (countLit q [-64, -70, -71, -73]) (count1593 q) 2 (meaning1583 q) (meaning1594 q) hs
  change valuationOf q 1583 = false ∨ valuationOf q 1594 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1256 (q : Snake 81) (h : Conditions q) : valuation q 1583 = false ∨ valuation q 1594 = true := counterClause1256 (baseVal q)

theorem counterClause1257 (q : Nat → Bool) : valuationOf q 1583 = false ∨ valuationOf q 1589 = false ∨ valuationOf q 1595 = true := by
  have hs : count1593 q = (countLit q [-61, -62, -63]) + (countLit q [-64, -70, -71, -73]) := List.countP_append (p := literal q) (l₁ := [-61, -62, -63]) (l₂ := [-64, -70, -71, -73])
  have hm := merge_two (literal (valuationOf q) (1583)) (literal (valuationOf q) (1589)) (literal (valuationOf q) (1595)) (countLit q [-61, -62, -63]) (countLit q [-64, -70, -71, -73]) (count1593 q) 2 1 (meaning1583 q) (meaning1589 q) (meaning1595 q) hs
  change valuationOf q 1583 = false ∨ valuationOf q 1589 = false ∨ valuationOf q 1595 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1257 (q : Snake 81) (h : Conditions q) : valuation q 1583 = false ∨ valuation q 1589 = false ∨ valuation q 1595 = true := counterClause1257 (baseVal q)

theorem counterClause1258 (q : Nat → Bool) : valuationOf q 1583 = false ∨ valuationOf q 1590 = false ∨ valuationOf q 1596 = true := by
  have hs : count1593 q = (countLit q [-61, -62, -63]) + (countLit q [-64, -70, -71, -73]) := List.countP_append (p := literal q) (l₁ := [-61, -62, -63]) (l₂ := [-64, -70, -71, -73])
  have hm := merge_two (literal (valuationOf q) (1583)) (literal (valuationOf q) (1590)) (literal (valuationOf q) (1596)) (countLit q [-61, -62, -63]) (countLit q [-64, -70, -71, -73]) (count1593 q) 2 2 (meaning1583 q) (meaning1590 q) (meaning1596 q) hs
  change valuationOf q 1583 = false ∨ valuationOf q 1590 = false ∨ valuationOf q 1596 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1258 (q : Snake 81) (h : Conditions q) : valuation q 1583 = false ∨ valuation q 1590 = false ∨ valuation q 1596 = true := counterClause1258 (baseVal q)

theorem counterClause1259 (q : Nat → Bool) : valuationOf q 1584 = false ∨ valuationOf q 1592 = false ∨ valuationOf q 1599 = true := by
  have hs : count1593 q = (countLit q [-61, -62, -63]) + (countLit q [-64, -70, -71, -73]) := List.countP_append (p := literal q) (l₁ := [-61, -62, -63]) (l₂ := [-64, -70, -71, -73])
  have hm := merge_two (literal (valuationOf q) (1584)) (literal (valuationOf q) (1592)) (literal (valuationOf q) (1599)) (countLit q [-61, -62, -63]) (countLit q [-64, -70, -71, -73]) (count1593 q) 3 4 (meaning1584 q) (meaning1592 q) (meaning1599 q) hs
  change valuationOf q 1584 = false ∨ valuationOf q 1592 = false ∨ valuationOf q 1599 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1259 (q : Snake 81) (h : Conditions q) : valuation q 1584 = false ∨ valuation q 1592 = false ∨ valuation q 1599 = true := counterClause1259 (baseVal q)

theorem counterClause1260 (q : Nat → Bool) : valuationOf q 77 = true ∨ valuationOf q 1600 = true := by
  have hs : count1600 q = (countLit q [-76]) + (countLit q [-77]) := List.countP_append (p := literal q) (l₁ := [-76]) (l₂ := [-77])
  have hm := merge_right (literal (valuationOf q) (-77)) (literal (valuationOf q) (1600)) (countLit q [-76]) (countLit q [-77]) (count1600 q) 1 (meaningNeg77 q) (meaning1600 q) hs
  change (! (valuationOf q 77)) = false ∨ valuationOf q 1600 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1260 (q : Snake 81) (h : Conditions q) : valuation q 77 = true ∨ valuation q 1600 = true := counterClause1260 (baseVal q)

theorem counterClause1261 (q : Nat → Bool) : valuationOf q 76 = true ∨ valuationOf q 1600 = true := by
  have hs : count1600 q = (countLit q [-76]) + (countLit q [-77]) := List.countP_append (p := literal q) (l₁ := [-76]) (l₂ := [-77])
  have hm := merge_left (literal (valuationOf q) (-76)) (literal (valuationOf q) (1600)) (countLit q [-76]) (countLit q [-77]) (count1600 q) 1 (meaningNeg76 q) (meaning1600 q) hs
  change (! (valuationOf q 76)) = false ∨ valuationOf q 1600 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1261 (q : Snake 81) (h : Conditions q) : valuation q 76 = true ∨ valuation q 1600 = true := counterClause1261 (baseVal q)

theorem counterClause1262 (q : Nat → Bool) : valuationOf q 76 = true ∨ valuationOf q 77 = true ∨ valuationOf q 1601 = true := by
  have hs : count1600 q = (countLit q [-76]) + (countLit q [-77]) := List.countP_append (p := literal q) (l₁ := [-76]) (l₂ := [-77])
  have hm := merge_two (literal (valuationOf q) (-76)) (literal (valuationOf q) (-77)) (literal (valuationOf q) (1601)) (countLit q [-76]) (countLit q [-77]) (count1600 q) 1 1 (meaningNeg76 q) (meaningNeg77 q) (meaning1601 q) hs
  change (! (valuationOf q 76)) = false ∨ (! (valuationOf q 77)) = false ∨ valuationOf q 1601 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1262 (q : Snake 81) (h : Conditions q) : valuation q 76 = true ∨ valuation q 77 = true ∨ valuation q 1601 = true := counterClause1262 (baseVal q)

theorem counterClause1263 (q : Nat → Bool) : valuationOf q 80 = true ∨ valuationOf q 1602 = true := by
  have hs : count1602 q = (countLit q [-79]) + (countLit q [-80]) := List.countP_append (p := literal q) (l₁ := [-79]) (l₂ := [-80])
  have hm := merge_right (literal (valuationOf q) (-80)) (literal (valuationOf q) (1602)) (countLit q [-79]) (countLit q [-80]) (count1602 q) 1 (meaningNeg80 q) (meaning1602 q) hs
  change (! (valuationOf q 80)) = false ∨ valuationOf q 1602 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1263 (q : Snake 81) (h : Conditions q) : valuation q 80 = true ∨ valuation q 1602 = true := counterClause1263 (baseVal q)

theorem counterClause1264 (q : Nat → Bool) : valuationOf q 79 = true ∨ valuationOf q 1602 = true := by
  have hs : count1602 q = (countLit q [-79]) + (countLit q [-80]) := List.countP_append (p := literal q) (l₁ := [-79]) (l₂ := [-80])
  have hm := merge_left (literal (valuationOf q) (-79)) (literal (valuationOf q) (1602)) (countLit q [-79]) (countLit q [-80]) (count1602 q) 1 (meaningNeg79 q) (meaning1602 q) hs
  change (! (valuationOf q 79)) = false ∨ valuationOf q 1602 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1264 (q : Snake 81) (h : Conditions q) : valuation q 79 = true ∨ valuation q 1602 = true := counterClause1264 (baseVal q)

theorem counterClause1265 (q : Nat → Bool) : valuationOf q 79 = true ∨ valuationOf q 80 = true ∨ valuationOf q 1603 = true := by
  have hs : count1602 q = (countLit q [-79]) + (countLit q [-80]) := List.countP_append (p := literal q) (l₁ := [-79]) (l₂ := [-80])
  have hm := merge_two (literal (valuationOf q) (-79)) (literal (valuationOf q) (-80)) (literal (valuationOf q) (1603)) (countLit q [-79]) (countLit q [-80]) (count1602 q) 1 1 (meaningNeg79 q) (meaningNeg80 q) (meaning1603 q) hs
  change (! (valuationOf q 79)) = false ∨ (! (valuationOf q 80)) = false ∨ valuationOf q 1603 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1265 (q : Snake 81) (h : Conditions q) : valuation q 79 = true ∨ valuation q 80 = true ∨ valuation q 1603 = true := counterClause1265 (baseVal q)

theorem counterClause1266 (q : Nat → Bool) : valuationOf q 1602 = false ∨ valuationOf q 1604 = true := by
  have hs : count1604 q = (countLit q [-76, -77]) + (countLit q [-79, -80]) := List.countP_append (p := literal q) (l₁ := [-76, -77]) (l₂ := [-79, -80])
  have hm := merge_right (literal (valuationOf q) (1602)) (literal (valuationOf q) (1604)) (countLit q [-76, -77]) (countLit q [-79, -80]) (count1604 q) 1 (meaning1602 q) (meaning1604 q) hs
  change valuationOf q 1602 = false ∨ valuationOf q 1604 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1266 (q : Snake 81) (h : Conditions q) : valuation q 1602 = false ∨ valuation q 1604 = true := counterClause1266 (baseVal q)

theorem counterClause1267 (q : Nat → Bool) : valuationOf q 1603 = false ∨ valuationOf q 1605 = true := by
  have hs : count1604 q = (countLit q [-76, -77]) + (countLit q [-79, -80]) := List.countP_append (p := literal q) (l₁ := [-76, -77]) (l₂ := [-79, -80])
  have hm := merge_right (literal (valuationOf q) (1603)) (literal (valuationOf q) (1605)) (countLit q [-76, -77]) (countLit q [-79, -80]) (count1604 q) 2 (meaning1603 q) (meaning1605 q) hs
  change valuationOf q 1603 = false ∨ valuationOf q 1605 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1267 (q : Snake 81) (h : Conditions q) : valuation q 1603 = false ∨ valuation q 1605 = true := counterClause1267 (baseVal q)

theorem counterClause1268 (q : Nat → Bool) : valuationOf q 1600 = false ∨ valuationOf q 1604 = true := by
  have hs : count1604 q = (countLit q [-76, -77]) + (countLit q [-79, -80]) := List.countP_append (p := literal q) (l₁ := [-76, -77]) (l₂ := [-79, -80])
  have hm := merge_left (literal (valuationOf q) (1600)) (literal (valuationOf q) (1604)) (countLit q [-76, -77]) (countLit q [-79, -80]) (count1604 q) 1 (meaning1600 q) (meaning1604 q) hs
  change valuationOf q 1600 = false ∨ valuationOf q 1604 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1268 (q : Snake 81) (h : Conditions q) : valuation q 1600 = false ∨ valuation q 1604 = true := counterClause1268 (baseVal q)

theorem counterClause1269 (q : Nat → Bool) : valuationOf q 1600 = false ∨ valuationOf q 1602 = false ∨ valuationOf q 1605 = true := by
  have hs : count1604 q = (countLit q [-76, -77]) + (countLit q [-79, -80]) := List.countP_append (p := literal q) (l₁ := [-76, -77]) (l₂ := [-79, -80])
  have hm := merge_two (literal (valuationOf q) (1600)) (literal (valuationOf q) (1602)) (literal (valuationOf q) (1605)) (countLit q [-76, -77]) (countLit q [-79, -80]) (count1604 q) 1 1 (meaning1600 q) (meaning1602 q) (meaning1605 q) hs
  change valuationOf q 1600 = false ∨ valuationOf q 1602 = false ∨ valuationOf q 1605 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1269 (q : Snake 81) (h : Conditions q) : valuation q 1600 = false ∨ valuation q 1602 = false ∨ valuation q 1605 = true := counterClause1269 (baseVal q)

theorem counterClause1270 (q : Nat → Bool) : valuationOf q 1600 = false ∨ valuationOf q 1603 = false ∨ valuationOf q 1606 = true := by
  have hs : count1604 q = (countLit q [-76, -77]) + (countLit q [-79, -80]) := List.countP_append (p := literal q) (l₁ := [-76, -77]) (l₂ := [-79, -80])
  have hm := merge_two (literal (valuationOf q) (1600)) (literal (valuationOf q) (1603)) (literal (valuationOf q) (1606)) (countLit q [-76, -77]) (countLit q [-79, -80]) (count1604 q) 1 2 (meaning1600 q) (meaning1603 q) (meaning1606 q) hs
  change valuationOf q 1600 = false ∨ valuationOf q 1603 = false ∨ valuationOf q 1606 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1270 (q : Snake 81) (h : Conditions q) : valuation q 1600 = false ∨ valuation q 1603 = false ∨ valuation q 1606 = true := counterClause1270 (baseVal q)

theorem counterClause1271 (q : Nat → Bool) : valuationOf q 1601 = false ∨ valuationOf q 1605 = true := by
  have hs : count1604 q = (countLit q [-76, -77]) + (countLit q [-79, -80]) := List.countP_append (p := literal q) (l₁ := [-76, -77]) (l₂ := [-79, -80])
  have hm := merge_left (literal (valuationOf q) (1601)) (literal (valuationOf q) (1605)) (countLit q [-76, -77]) (countLit q [-79, -80]) (count1604 q) 2 (meaning1601 q) (meaning1605 q) hs
  change valuationOf q 1601 = false ∨ valuationOf q 1605 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1271 (q : Snake 81) (h : Conditions q) : valuation q 1601 = false ∨ valuation q 1605 = true := counterClause1271 (baseVal q)

theorem counterClause1272 (q : Nat → Bool) : valuationOf q 1601 = false ∨ valuationOf q 1602 = false ∨ valuationOf q 1606 = true := by
  have hs : count1604 q = (countLit q [-76, -77]) + (countLit q [-79, -80]) := List.countP_append (p := literal q) (l₁ := [-76, -77]) (l₂ := [-79, -80])
  have hm := merge_two (literal (valuationOf q) (1601)) (literal (valuationOf q) (1602)) (literal (valuationOf q) (1606)) (countLit q [-76, -77]) (countLit q [-79, -80]) (count1604 q) 2 1 (meaning1601 q) (meaning1602 q) (meaning1606 q) hs
  change valuationOf q 1601 = false ∨ valuationOf q 1602 = false ∨ valuationOf q 1606 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1272 (q : Snake 81) (h : Conditions q) : valuation q 1601 = false ∨ valuation q 1602 = false ∨ valuation q 1606 = true := counterClause1272 (baseVal q)

theorem counterClause1273 (q : Nat → Bool) : valuationOf q 85 = true ∨ valuationOf q 1608 = true := by
  have hs : count1608 q = (countLit q [-82]) + (countLit q [-85]) := List.countP_append (p := literal q) (l₁ := [-82]) (l₂ := [-85])
  have hm := merge_right (literal (valuationOf q) (-85)) (literal (valuationOf q) (1608)) (countLit q [-82]) (countLit q [-85]) (count1608 q) 1 (meaningNeg85 q) (meaning1608 q) hs
  change (! (valuationOf q 85)) = false ∨ valuationOf q 1608 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1273 (q : Snake 81) (h : Conditions q) : valuation q 85 = true ∨ valuation q 1608 = true := counterClause1273 (baseVal q)

theorem counterClause1274 (q : Nat → Bool) : valuationOf q 82 = true ∨ valuationOf q 1608 = true := by
  have hs : count1608 q = (countLit q [-82]) + (countLit q [-85]) := List.countP_append (p := literal q) (l₁ := [-82]) (l₂ := [-85])
  have hm := merge_left (literal (valuationOf q) (-82)) (literal (valuationOf q) (1608)) (countLit q [-82]) (countLit q [-85]) (count1608 q) 1 (meaningNeg82 q) (meaning1608 q) hs
  change (! (valuationOf q 82)) = false ∨ valuationOf q 1608 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1274 (q : Snake 81) (h : Conditions q) : valuation q 82 = true ∨ valuation q 1608 = true := counterClause1274 (baseVal q)

theorem counterClause1275 (q : Nat → Bool) : valuationOf q 82 = true ∨ valuationOf q 85 = true ∨ valuationOf q 1609 = true := by
  have hs : count1608 q = (countLit q [-82]) + (countLit q [-85]) := List.countP_append (p := literal q) (l₁ := [-82]) (l₂ := [-85])
  have hm := merge_two (literal (valuationOf q) (-82)) (literal (valuationOf q) (-85)) (literal (valuationOf q) (1609)) (countLit q [-82]) (countLit q [-85]) (count1608 q) 1 1 (meaningNeg82 q) (meaningNeg85 q) (meaning1609 q) hs
  change (! (valuationOf q 82)) = false ∨ (! (valuationOf q 85)) = false ∨ valuationOf q 1609 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1275 (q : Snake 81) (h : Conditions q) : valuation q 82 = true ∨ valuation q 85 = true ∨ valuation q 1609 = true := counterClause1275 (baseVal q)

theorem counterClause1276 (q : Nat → Bool) : valuationOf q 88 = true ∨ valuationOf q 1610 = true := by
  have hs : count1610 q = (countLit q [-87]) + (countLit q [-88]) := List.countP_append (p := literal q) (l₁ := [-87]) (l₂ := [-88])
  have hm := merge_right (literal (valuationOf q) (-88)) (literal (valuationOf q) (1610)) (countLit q [-87]) (countLit q [-88]) (count1610 q) 1 (meaningNeg88 q) (meaning1610 q) hs
  change (! (valuationOf q 88)) = false ∨ valuationOf q 1610 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1276 (q : Snake 81) (h : Conditions q) : valuation q 88 = true ∨ valuation q 1610 = true := counterClause1276 (baseVal q)

theorem counterClause1277 (q : Nat → Bool) : valuationOf q 87 = true ∨ valuationOf q 1610 = true := by
  have hs : count1610 q = (countLit q [-87]) + (countLit q [-88]) := List.countP_append (p := literal q) (l₁ := [-87]) (l₂ := [-88])
  have hm := merge_left (literal (valuationOf q) (-87)) (literal (valuationOf q) (1610)) (countLit q [-87]) (countLit q [-88]) (count1610 q) 1 (meaningNeg87 q) (meaning1610 q) hs
  change (! (valuationOf q 87)) = false ∨ valuationOf q 1610 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1277 (q : Snake 81) (h : Conditions q) : valuation q 87 = true ∨ valuation q 1610 = true := counterClause1277 (baseVal q)

theorem counterClause1278 (q : Nat → Bool) : valuationOf q 87 = true ∨ valuationOf q 88 = true ∨ valuationOf q 1611 = true := by
  have hs : count1610 q = (countLit q [-87]) + (countLit q [-88]) := List.countP_append (p := literal q) (l₁ := [-87]) (l₂ := [-88])
  have hm := merge_two (literal (valuationOf q) (-87)) (literal (valuationOf q) (-88)) (literal (valuationOf q) (1611)) (countLit q [-87]) (countLit q [-88]) (count1610 q) 1 1 (meaningNeg87 q) (meaningNeg88 q) (meaning1611 q) hs
  change (! (valuationOf q 87)) = false ∨ (! (valuationOf q 88)) = false ∨ valuationOf q 1611 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1278 (q : Snake 81) (h : Conditions q) : valuation q 87 = true ∨ valuation q 88 = true ∨ valuation q 1611 = true := counterClause1278 (baseVal q)

theorem counterClause1279 (q : Nat → Bool) : valuationOf q 1610 = false ∨ valuationOf q 1612 = true := by
  have hs : count1612 q = (countLit q [-82, -85]) + (countLit q [-87, -88]) := List.countP_append (p := literal q) (l₁ := [-82, -85]) (l₂ := [-87, -88])
  have hm := merge_right (literal (valuationOf q) (1610)) (literal (valuationOf q) (1612)) (countLit q [-82, -85]) (countLit q [-87, -88]) (count1612 q) 1 (meaning1610 q) (meaning1612 q) hs
  change valuationOf q 1610 = false ∨ valuationOf q 1612 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1279 (q : Snake 81) (h : Conditions q) : valuation q 1610 = false ∨ valuation q 1612 = true := counterClause1279 (baseVal q)

theorem counterClause1280 (q : Nat → Bool) : valuationOf q 1611 = false ∨ valuationOf q 1613 = true := by
  have hs : count1612 q = (countLit q [-82, -85]) + (countLit q [-87, -88]) := List.countP_append (p := literal q) (l₁ := [-82, -85]) (l₂ := [-87, -88])
  have hm := merge_right (literal (valuationOf q) (1611)) (literal (valuationOf q) (1613)) (countLit q [-82, -85]) (countLit q [-87, -88]) (count1612 q) 2 (meaning1611 q) (meaning1613 q) hs
  change valuationOf q 1611 = false ∨ valuationOf q 1613 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1280 (q : Snake 81) (h : Conditions q) : valuation q 1611 = false ∨ valuation q 1613 = true := counterClause1280 (baseVal q)

theorem block39 (q : Snake 81) (h : Conditions q) : B112E040.Block39 (valuation q) :=
  ⟨clause1249 q h, clause1250 q h, clause1251 q h, clause1252 q h, clause1253 q h, clause1254 q h, clause1255 q h, clause1256 q h, clause1257 q h, clause1258 q h, clause1259 q h, clause1260 q h, clause1261 q h, clause1262 q h, clause1263 q h, clause1264 q h, clause1265 q h, clause1266 q h, clause1267 q h, clause1268 q h, clause1269 q h, clause1270 q h, clause1271 q h, clause1272 q h, clause1273 q h, clause1274 q h, clause1275 q h, clause1276 q h, clause1277 q h, clause1278 q h, clause1279 q h, clause1280 q h⟩

end
end Snake9.Regrowth.E112040
