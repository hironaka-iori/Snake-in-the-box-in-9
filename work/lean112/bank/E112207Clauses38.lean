import E112207Semantics
import B112E207Inputs
namespace Snake9.Regrowth.E112207
noncomputable section
local instance blockDec38 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1217 (q : Nat → Bool) : valuationOf q 1557 = false ∨ valuationOf q 1576 = false ∨ valuationOf q 1586 = true := by
  have hs : count1582 q = (countLit q [-62, -63, -66, -69, -71, -72, -74]) + (countLit q [-75, -79, -80, -81, -82, -86, -89]) := List.countP_append (p := literal q) (l₁ := [-62, -63, -66, -69, -71, -72, -74]) (l₂ := [-75, -79, -80, -81, -82, -86, -89])
  have hm := merge_two (literal (valuationOf q) (1557)) (literal (valuationOf q) (1576)) (literal (valuationOf q) (1586)) (countLit q [-62, -63, -66, -69, -71, -72, -74]) (countLit q [-75, -79, -80, -81, -82, -86, -89]) (count1582 q) 3 2 (meaning1557 q) (meaning1576 q) (meaning1586 q) hs
  change valuationOf q 1557 = false ∨ valuationOf q 1576 = false ∨ valuationOf q 1586 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1217 (q : Snake 81) (h : Conditions q) : valuation q 1557 = false ∨ valuation q 1576 = false ∨ valuation q 1586 = true := counterClause1217 (baseVal q)

theorem counterClause1218 (q : Nat → Bool) : valuationOf q 1557 = false ∨ valuationOf q 1577 = false ∨ valuationOf q 1587 = true := by
  have hs : count1582 q = (countLit q [-62, -63, -66, -69, -71, -72, -74]) + (countLit q [-75, -79, -80, -81, -82, -86, -89]) := List.countP_append (p := literal q) (l₁ := [-62, -63, -66, -69, -71, -72, -74]) (l₂ := [-75, -79, -80, -81, -82, -86, -89])
  have hm := merge_two (literal (valuationOf q) (1557)) (literal (valuationOf q) (1577)) (literal (valuationOf q) (1587)) (countLit q [-62, -63, -66, -69, -71, -72, -74]) (countLit q [-75, -79, -80, -81, -82, -86, -89]) (count1582 q) 3 3 (meaning1557 q) (meaning1577 q) (meaning1587 q) hs
  change valuationOf q 1557 = false ∨ valuationOf q 1577 = false ∨ valuationOf q 1587 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1218 (q : Snake 81) (h : Conditions q) : valuation q 1557 = false ∨ valuation q 1577 = false ∨ valuation q 1587 = true := counterClause1218 (baseVal q)

theorem counterClause1219 (q : Nat → Bool) : valuationOf q 1558 = false ∨ valuationOf q 1575 = false ∨ valuationOf q 1586 = true := by
  have hs : count1582 q = (countLit q [-62, -63, -66, -69, -71, -72, -74]) + (countLit q [-75, -79, -80, -81, -82, -86, -89]) := List.countP_append (p := literal q) (l₁ := [-62, -63, -66, -69, -71, -72, -74]) (l₂ := [-75, -79, -80, -81, -82, -86, -89])
  have hm := merge_two (literal (valuationOf q) (1558)) (literal (valuationOf q) (1575)) (literal (valuationOf q) (1586)) (countLit q [-62, -63, -66, -69, -71, -72, -74]) (countLit q [-75, -79, -80, -81, -82, -86, -89]) (count1582 q) 4 1 (meaning1558 q) (meaning1575 q) (meaning1586 q) hs
  change valuationOf q 1558 = false ∨ valuationOf q 1575 = false ∨ valuationOf q 1586 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1219 (q : Snake 81) (h : Conditions q) : valuation q 1558 = false ∨ valuation q 1575 = false ∨ valuation q 1586 = true := counterClause1219 (baseVal q)

theorem counterClause1220 (q : Nat → Bool) : valuationOf q 1558 = false ∨ valuationOf q 1576 = false ∨ valuationOf q 1587 = true := by
  have hs : count1582 q = (countLit q [-62, -63, -66, -69, -71, -72, -74]) + (countLit q [-75, -79, -80, -81, -82, -86, -89]) := List.countP_append (p := literal q) (l₁ := [-62, -63, -66, -69, -71, -72, -74]) (l₂ := [-75, -79, -80, -81, -82, -86, -89])
  have hm := merge_two (literal (valuationOf q) (1558)) (literal (valuationOf q) (1576)) (literal (valuationOf q) (1587)) (countLit q [-62, -63, -66, -69, -71, -72, -74]) (countLit q [-75, -79, -80, -81, -82, -86, -89]) (count1582 q) 4 2 (meaning1558 q) (meaning1576 q) (meaning1587 q) hs
  change valuationOf q 1558 = false ∨ valuationOf q 1576 = false ∨ valuationOf q 1587 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1220 (q : Snake 81) (h : Conditions q) : valuation q 1558 = false ∨ valuation q 1576 = false ∨ valuation q 1587 = true := counterClause1220 (baseVal q)

theorem counterClause1221 (q : Nat → Bool) : valuationOf q 1558 = false ∨ valuationOf q 1577 = false ∨ valuationOf q 1588 = true := by
  have hs : count1582 q = (countLit q [-62, -63, -66, -69, -71, -72, -74]) + (countLit q [-75, -79, -80, -81, -82, -86, -89]) := List.countP_append (p := literal q) (l₁ := [-62, -63, -66, -69, -71, -72, -74]) (l₂ := [-75, -79, -80, -81, -82, -86, -89])
  have hm := merge_two (literal (valuationOf q) (1558)) (literal (valuationOf q) (1577)) (literal (valuationOf q) (1588)) (countLit q [-62, -63, -66, -69, -71, -72, -74]) (countLit q [-75, -79, -80, -81, -82, -86, -89]) (count1582 q) 4 3 (meaning1558 q) (meaning1577 q) (meaning1588 q) hs
  change valuationOf q 1558 = false ∨ valuationOf q 1577 = false ∨ valuationOf q 1588 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1221 (q : Snake 81) (h : Conditions q) : valuation q 1558 = false ∨ valuation q 1577 = false ∨ valuation q 1588 = true := counterClause1221 (baseVal q)

theorem counterClause1222 (q : Nat → Bool) : valuationOf q 1559 = false ∨ valuationOf q 1575 = false ∨ valuationOf q 1587 = true := by
  have hs : count1582 q = (countLit q [-62, -63, -66, -69, -71, -72, -74]) + (countLit q [-75, -79, -80, -81, -82, -86, -89]) := List.countP_append (p := literal q) (l₁ := [-62, -63, -66, -69, -71, -72, -74]) (l₂ := [-75, -79, -80, -81, -82, -86, -89])
  have hm := merge_two (literal (valuationOf q) (1559)) (literal (valuationOf q) (1575)) (literal (valuationOf q) (1587)) (countLit q [-62, -63, -66, -69, -71, -72, -74]) (countLit q [-75, -79, -80, -81, -82, -86, -89]) (count1582 q) 5 1 (meaning1559 q) (meaning1575 q) (meaning1587 q) hs
  change valuationOf q 1559 = false ∨ valuationOf q 1575 = false ∨ valuationOf q 1587 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1222 (q : Snake 81) (h : Conditions q) : valuation q 1559 = false ∨ valuation q 1575 = false ∨ valuation q 1587 = true := counterClause1222 (baseVal q)

theorem counterClause1223 (q : Nat → Bool) : valuationOf q 1559 = false ∨ valuationOf q 1576 = false ∨ valuationOf q 1588 = true := by
  have hs : count1582 q = (countLit q [-62, -63, -66, -69, -71, -72, -74]) + (countLit q [-75, -79, -80, -81, -82, -86, -89]) := List.countP_append (p := literal q) (l₁ := [-62, -63, -66, -69, -71, -72, -74]) (l₂ := [-75, -79, -80, -81, -82, -86, -89])
  have hm := merge_two (literal (valuationOf q) (1559)) (literal (valuationOf q) (1576)) (literal (valuationOf q) (1588)) (countLit q [-62, -63, -66, -69, -71, -72, -74]) (countLit q [-75, -79, -80, -81, -82, -86, -89]) (count1582 q) 5 2 (meaning1559 q) (meaning1576 q) (meaning1588 q) hs
  change valuationOf q 1559 = false ∨ valuationOf q 1576 = false ∨ valuationOf q 1588 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1223 (q : Snake 81) (h : Conditions q) : valuation q 1559 = false ∨ valuation q 1576 = false ∨ valuation q 1588 = true := counterClause1223 (baseVal q)

theorem counterClause1224 (q : Nat → Bool) : valuationOf q 1560 = false ∨ valuationOf q 1575 = false ∨ valuationOf q 1588 = true := by
  have hs : count1582 q = (countLit q [-62, -63, -66, -69, -71, -72, -74]) + (countLit q [-75, -79, -80, -81, -82, -86, -89]) := List.countP_append (p := literal q) (l₁ := [-62, -63, -66, -69, -71, -72, -74]) (l₂ := [-75, -79, -80, -81, -82, -86, -89])
  have hm := merge_two (literal (valuationOf q) (1560)) (literal (valuationOf q) (1575)) (literal (valuationOf q) (1588)) (countLit q [-62, -63, -66, -69, -71, -72, -74]) (countLit q [-75, -79, -80, -81, -82, -86, -89]) (count1582 q) 6 1 (meaning1560 q) (meaning1575 q) (meaning1588 q) hs
  change valuationOf q 1560 = false ∨ valuationOf q 1575 = false ∨ valuationOf q 1588 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1224 (q : Snake 81) (h : Conditions q) : valuation q 1560 = false ∨ valuation q 1575 = false ∨ valuation q 1588 = true := counterClause1224 (baseVal q)

theorem counterClause1225 (q : Nat → Bool) : valuationOf q 93 = true ∨ valuationOf q 1596 = true := by
  have hs : count1596 q = (countLit q [-92]) + (countLit q [-93]) := List.countP_append (p := literal q) (l₁ := [-92]) (l₂ := [-93])
  have hm := merge_right (literal (valuationOf q) (-93)) (literal (valuationOf q) (1596)) (countLit q [-92]) (countLit q [-93]) (count1596 q) 1 (meaningNeg93 q) (meaning1596 q) hs
  change (! (valuationOf q 93)) = false ∨ valuationOf q 1596 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1225 (q : Snake 81) (h : Conditions q) : valuation q 93 = true ∨ valuation q 1596 = true := counterClause1225 (baseVal q)

theorem counterClause1226 (q : Nat → Bool) : valuationOf q 92 = true ∨ valuationOf q 1596 = true := by
  have hs : count1596 q = (countLit q [-92]) + (countLit q [-93]) := List.countP_append (p := literal q) (l₁ := [-92]) (l₂ := [-93])
  have hm := merge_left (literal (valuationOf q) (-92)) (literal (valuationOf q) (1596)) (countLit q [-92]) (countLit q [-93]) (count1596 q) 1 (meaningNeg92 q) (meaning1596 q) hs
  change (! (valuationOf q 92)) = false ∨ valuationOf q 1596 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1226 (q : Snake 81) (h : Conditions q) : valuation q 92 = true ∨ valuation q 1596 = true := counterClause1226 (baseVal q)

theorem counterClause1227 (q : Nat → Bool) : valuationOf q 92 = true ∨ valuationOf q 93 = true ∨ valuationOf q 1597 = true := by
  have hs : count1596 q = (countLit q [-92]) + (countLit q [-93]) := List.countP_append (p := literal q) (l₁ := [-92]) (l₂ := [-93])
  have hm := merge_two (literal (valuationOf q) (-92)) (literal (valuationOf q) (-93)) (literal (valuationOf q) (1597)) (countLit q [-92]) (countLit q [-93]) (count1596 q) 1 1 (meaningNeg92 q) (meaningNeg93 q) (meaning1597 q) hs
  change (! (valuationOf q 92)) = false ∨ (! (valuationOf q 93)) = false ∨ valuationOf q 1597 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1227 (q : Snake 81) (h : Conditions q) : valuation q 92 = true ∨ valuation q 93 = true ∨ valuation q 1597 = true := counterClause1227 (baseVal q)

theorem counterClause1228 (q : Nat → Bool) : valuationOf q 1596 = false ∨ valuationOf q 1598 = true := by
  have hs : count1598 q = (countLit q [-90]) + (countLit q [-92, -93]) := List.countP_append (p := literal q) (l₁ := [-90]) (l₂ := [-92, -93])
  have hm := merge_right (literal (valuationOf q) (1596)) (literal (valuationOf q) (1598)) (countLit q [-90]) (countLit q [-92, -93]) (count1598 q) 1 (meaning1596 q) (meaning1598 q) hs
  change valuationOf q 1596 = false ∨ valuationOf q 1598 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1228 (q : Snake 81) (h : Conditions q) : valuation q 1596 = false ∨ valuation q 1598 = true := counterClause1228 (baseVal q)

theorem counterClause1229 (q : Nat → Bool) : valuationOf q 1597 = false ∨ valuationOf q 1599 = true := by
  have hs : count1598 q = (countLit q [-90]) + (countLit q [-92, -93]) := List.countP_append (p := literal q) (l₁ := [-90]) (l₂ := [-92, -93])
  have hm := merge_right (literal (valuationOf q) (1597)) (literal (valuationOf q) (1599)) (countLit q [-90]) (countLit q [-92, -93]) (count1598 q) 2 (meaning1597 q) (meaning1599 q) hs
  change valuationOf q 1597 = false ∨ valuationOf q 1599 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1229 (q : Snake 81) (h : Conditions q) : valuation q 1597 = false ∨ valuation q 1599 = true := counterClause1229 (baseVal q)

theorem counterClause1230 (q : Nat → Bool) : valuationOf q 90 = true ∨ valuationOf q 1598 = true := by
  have hs : count1598 q = (countLit q [-90]) + (countLit q [-92, -93]) := List.countP_append (p := literal q) (l₁ := [-90]) (l₂ := [-92, -93])
  have hm := merge_left (literal (valuationOf q) (-90)) (literal (valuationOf q) (1598)) (countLit q [-90]) (countLit q [-92, -93]) (count1598 q) 1 (meaningNeg90 q) (meaning1598 q) hs
  change (! (valuationOf q 90)) = false ∨ valuationOf q 1598 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1230 (q : Snake 81) (h : Conditions q) : valuation q 90 = true ∨ valuation q 1598 = true := counterClause1230 (baseVal q)

theorem counterClause1231 (q : Nat → Bool) : valuationOf q 90 = true ∨ valuationOf q 1596 = false ∨ valuationOf q 1599 = true := by
  have hs : count1598 q = (countLit q [-90]) + (countLit q [-92, -93]) := List.countP_append (p := literal q) (l₁ := [-90]) (l₂ := [-92, -93])
  have hm := merge_two (literal (valuationOf q) (-90)) (literal (valuationOf q) (1596)) (literal (valuationOf q) (1599)) (countLit q [-90]) (countLit q [-92, -93]) (count1598 q) 1 1 (meaningNeg90 q) (meaning1596 q) (meaning1599 q) hs
  change (! (valuationOf q 90)) = false ∨ valuationOf q 1596 = false ∨ valuationOf q 1599 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1231 (q : Snake 81) (h : Conditions q) : valuation q 90 = true ∨ valuation q 1596 = false ∨ valuation q 1599 = true := counterClause1231 (baseVal q)

theorem counterClause1232 (q : Nat → Bool) : valuationOf q 90 = true ∨ valuationOf q 1597 = false ∨ valuationOf q 1600 = true := by
  have hs : count1598 q = (countLit q [-90]) + (countLit q [-92, -93]) := List.countP_append (p := literal q) (l₁ := [-90]) (l₂ := [-92, -93])
  have hm := merge_two (literal (valuationOf q) (-90)) (literal (valuationOf q) (1597)) (literal (valuationOf q) (1600)) (countLit q [-90]) (countLit q [-92, -93]) (count1598 q) 1 2 (meaningNeg90 q) (meaning1597 q) (meaning1600 q) hs
  change (! (valuationOf q 90)) = false ∨ valuationOf q 1597 = false ∨ valuationOf q 1600 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1232 (q : Snake 81) (h : Conditions q) : valuation q 90 = true ∨ valuation q 1597 = false ∨ valuation q 1600 = true := counterClause1232 (baseVal q)

theorem counterClause1233 (q : Nat → Bool) : valuationOf q 98 = true ∨ valuationOf q 1601 = true := by
  have hs : count1601 q = (countLit q [-95]) + (countLit q [-98]) := List.countP_append (p := literal q) (l₁ := [-95]) (l₂ := [-98])
  have hm := merge_right (literal (valuationOf q) (-98)) (literal (valuationOf q) (1601)) (countLit q [-95]) (countLit q [-98]) (count1601 q) 1 (meaningNeg98 q) (meaning1601 q) hs
  change (! (valuationOf q 98)) = false ∨ valuationOf q 1601 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1233 (q : Snake 81) (h : Conditions q) : valuation q 98 = true ∨ valuation q 1601 = true := counterClause1233 (baseVal q)

theorem counterClause1234 (q : Nat → Bool) : valuationOf q 95 = true ∨ valuationOf q 1601 = true := by
  have hs : count1601 q = (countLit q [-95]) + (countLit q [-98]) := List.countP_append (p := literal q) (l₁ := [-95]) (l₂ := [-98])
  have hm := merge_left (literal (valuationOf q) (-95)) (literal (valuationOf q) (1601)) (countLit q [-95]) (countLit q [-98]) (count1601 q) 1 (meaningNeg95 q) (meaning1601 q) hs
  change (! (valuationOf q 95)) = false ∨ valuationOf q 1601 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1234 (q : Snake 81) (h : Conditions q) : valuation q 95 = true ∨ valuation q 1601 = true := counterClause1234 (baseVal q)

theorem counterClause1235 (q : Nat → Bool) : valuationOf q 95 = true ∨ valuationOf q 98 = true ∨ valuationOf q 1602 = true := by
  have hs : count1601 q = (countLit q [-95]) + (countLit q [-98]) := List.countP_append (p := literal q) (l₁ := [-95]) (l₂ := [-98])
  have hm := merge_two (literal (valuationOf q) (-95)) (literal (valuationOf q) (-98)) (literal (valuationOf q) (1602)) (countLit q [-95]) (countLit q [-98]) (count1601 q) 1 1 (meaningNeg95 q) (meaningNeg98 q) (meaning1602 q) hs
  change (! (valuationOf q 95)) = false ∨ (! (valuationOf q 98)) = false ∨ valuationOf q 1602 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1235 (q : Snake 81) (h : Conditions q) : valuation q 95 = true ∨ valuation q 98 = true ∨ valuation q 1602 = true := counterClause1235 (baseVal q)

theorem counterClause1236 (q : Nat → Bool) : valuationOf q 100 = true ∨ valuationOf q 1603 = true := by
  have hs : count1603 q = (countLit q [-99]) + (countLit q [-100]) := List.countP_append (p := literal q) (l₁ := [-99]) (l₂ := [-100])
  have hm := merge_right (literal (valuationOf q) (-100)) (literal (valuationOf q) (1603)) (countLit q [-99]) (countLit q [-100]) (count1603 q) 1 (meaningNeg100 q) (meaning1603 q) hs
  change (! (valuationOf q 100)) = false ∨ valuationOf q 1603 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1236 (q : Snake 81) (h : Conditions q) : valuation q 100 = true ∨ valuation q 1603 = true := counterClause1236 (baseVal q)

theorem counterClause1237 (q : Nat → Bool) : valuationOf q 99 = true ∨ valuationOf q 1603 = true := by
  have hs : count1603 q = (countLit q [-99]) + (countLit q [-100]) := List.countP_append (p := literal q) (l₁ := [-99]) (l₂ := [-100])
  have hm := merge_left (literal (valuationOf q) (-99)) (literal (valuationOf q) (1603)) (countLit q [-99]) (countLit q [-100]) (count1603 q) 1 (meaningNeg99 q) (meaning1603 q) hs
  change (! (valuationOf q 99)) = false ∨ valuationOf q 1603 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1237 (q : Snake 81) (h : Conditions q) : valuation q 99 = true ∨ valuation q 1603 = true := counterClause1237 (baseVal q)

theorem counterClause1238 (q : Nat → Bool) : valuationOf q 99 = true ∨ valuationOf q 100 = true ∨ valuationOf q 1604 = true := by
  have hs : count1603 q = (countLit q [-99]) + (countLit q [-100]) := List.countP_append (p := literal q) (l₁ := [-99]) (l₂ := [-100])
  have hm := merge_two (literal (valuationOf q) (-99)) (literal (valuationOf q) (-100)) (literal (valuationOf q) (1604)) (countLit q [-99]) (countLit q [-100]) (count1603 q) 1 1 (meaningNeg99 q) (meaningNeg100 q) (meaning1604 q) hs
  change (! (valuationOf q 99)) = false ∨ (! (valuationOf q 100)) = false ∨ valuationOf q 1604 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1238 (q : Snake 81) (h : Conditions q) : valuation q 99 = true ∨ valuation q 100 = true ∨ valuation q 1604 = true := counterClause1238 (baseVal q)

theorem counterClause1239 (q : Nat → Bool) : valuationOf q 1603 = false ∨ valuationOf q 1605 = true := by
  have hs : count1605 q = (countLit q [-95, -98]) + (countLit q [-99, -100]) := List.countP_append (p := literal q) (l₁ := [-95, -98]) (l₂ := [-99, -100])
  have hm := merge_right (literal (valuationOf q) (1603)) (literal (valuationOf q) (1605)) (countLit q [-95, -98]) (countLit q [-99, -100]) (count1605 q) 1 (meaning1603 q) (meaning1605 q) hs
  change valuationOf q 1603 = false ∨ valuationOf q 1605 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1239 (q : Snake 81) (h : Conditions q) : valuation q 1603 = false ∨ valuation q 1605 = true := counterClause1239 (baseVal q)

theorem counterClause1240 (q : Nat → Bool) : valuationOf q 1604 = false ∨ valuationOf q 1606 = true := by
  have hs : count1605 q = (countLit q [-95, -98]) + (countLit q [-99, -100]) := List.countP_append (p := literal q) (l₁ := [-95, -98]) (l₂ := [-99, -100])
  have hm := merge_right (literal (valuationOf q) (1604)) (literal (valuationOf q) (1606)) (countLit q [-95, -98]) (countLit q [-99, -100]) (count1605 q) 2 (meaning1604 q) (meaning1606 q) hs
  change valuationOf q 1604 = false ∨ valuationOf q 1606 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1240 (q : Snake 81) (h : Conditions q) : valuation q 1604 = false ∨ valuation q 1606 = true := counterClause1240 (baseVal q)

theorem counterClause1241 (q : Nat → Bool) : valuationOf q 1601 = false ∨ valuationOf q 1605 = true := by
  have hs : count1605 q = (countLit q [-95, -98]) + (countLit q [-99, -100]) := List.countP_append (p := literal q) (l₁ := [-95, -98]) (l₂ := [-99, -100])
  have hm := merge_left (literal (valuationOf q) (1601)) (literal (valuationOf q) (1605)) (countLit q [-95, -98]) (countLit q [-99, -100]) (count1605 q) 1 (meaning1601 q) (meaning1605 q) hs
  change valuationOf q 1601 = false ∨ valuationOf q 1605 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1241 (q : Snake 81) (h : Conditions q) : valuation q 1601 = false ∨ valuation q 1605 = true := counterClause1241 (baseVal q)

theorem counterClause1242 (q : Nat → Bool) : valuationOf q 1601 = false ∨ valuationOf q 1603 = false ∨ valuationOf q 1606 = true := by
  have hs : count1605 q = (countLit q [-95, -98]) + (countLit q [-99, -100]) := List.countP_append (p := literal q) (l₁ := [-95, -98]) (l₂ := [-99, -100])
  have hm := merge_two (literal (valuationOf q) (1601)) (literal (valuationOf q) (1603)) (literal (valuationOf q) (1606)) (countLit q [-95, -98]) (countLit q [-99, -100]) (count1605 q) 1 1 (meaning1601 q) (meaning1603 q) (meaning1606 q) hs
  change valuationOf q 1601 = false ∨ valuationOf q 1603 = false ∨ valuationOf q 1606 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1242 (q : Snake 81) (h : Conditions q) : valuation q 1601 = false ∨ valuation q 1603 = false ∨ valuation q 1606 = true := counterClause1242 (baseVal q)

theorem counterClause1243 (q : Nat → Bool) : valuationOf q 1602 = false ∨ valuationOf q 1606 = true := by
  have hs : count1605 q = (countLit q [-95, -98]) + (countLit q [-99, -100]) := List.countP_append (p := literal q) (l₁ := [-95, -98]) (l₂ := [-99, -100])
  have hm := merge_left (literal (valuationOf q) (1602)) (literal (valuationOf q) (1606)) (countLit q [-95, -98]) (countLit q [-99, -100]) (count1605 q) 2 (meaning1602 q) (meaning1606 q) hs
  change valuationOf q 1602 = false ∨ valuationOf q 1606 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1243 (q : Snake 81) (h : Conditions q) : valuation q 1602 = false ∨ valuation q 1606 = true := counterClause1243 (baseVal q)

theorem counterClause1244 (q : Nat → Bool) : valuationOf q 1602 = false ∨ valuationOf q 1603 = false ∨ valuationOf q 1607 = true := by
  have hs : count1605 q = (countLit q [-95, -98]) + (countLit q [-99, -100]) := List.countP_append (p := literal q) (l₁ := [-95, -98]) (l₂ := [-99, -100])
  have hm := merge_two (literal (valuationOf q) (1602)) (literal (valuationOf q) (1603)) (literal (valuationOf q) (1607)) (countLit q [-95, -98]) (countLit q [-99, -100]) (count1605 q) 2 1 (meaning1602 q) (meaning1603 q) (meaning1607 q) hs
  change valuationOf q 1602 = false ∨ valuationOf q 1603 = false ∨ valuationOf q 1607 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1244 (q : Snake 81) (h : Conditions q) : valuation q 1602 = false ∨ valuation q 1603 = false ∨ valuation q 1607 = true := counterClause1244 (baseVal q)

theorem counterClause1245 (q : Nat → Bool) : valuationOf q 1605 = false ∨ valuationOf q 1609 = true := by
  have hs : count1609 q = (countLit q [-90, -92, -93]) + (countLit q [-95, -98, -99, -100]) := List.countP_append (p := literal q) (l₁ := [-90, -92, -93]) (l₂ := [-95, -98, -99, -100])
  have hm := merge_right (literal (valuationOf q) (1605)) (literal (valuationOf q) (1609)) (countLit q [-90, -92, -93]) (countLit q [-95, -98, -99, -100]) (count1609 q) 1 (meaning1605 q) (meaning1609 q) hs
  change valuationOf q 1605 = false ∨ valuationOf q 1609 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1245 (q : Snake 81) (h : Conditions q) : valuation q 1605 = false ∨ valuation q 1609 = true := counterClause1245 (baseVal q)

theorem counterClause1246 (q : Nat → Bool) : valuationOf q 1606 = false ∨ valuationOf q 1610 = true := by
  have hs : count1609 q = (countLit q [-90, -92, -93]) + (countLit q [-95, -98, -99, -100]) := List.countP_append (p := literal q) (l₁ := [-90, -92, -93]) (l₂ := [-95, -98, -99, -100])
  have hm := merge_right (literal (valuationOf q) (1606)) (literal (valuationOf q) (1610)) (countLit q [-90, -92, -93]) (countLit q [-95, -98, -99, -100]) (count1609 q) 2 (meaning1606 q) (meaning1610 q) hs
  change valuationOf q 1606 = false ∨ valuationOf q 1610 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1246 (q : Snake 81) (h : Conditions q) : valuation q 1606 = false ∨ valuation q 1610 = true := counterClause1246 (baseVal q)

theorem counterClause1247 (q : Nat → Bool) : valuationOf q 1607 = false ∨ valuationOf q 1611 = true := by
  have hs : count1609 q = (countLit q [-90, -92, -93]) + (countLit q [-95, -98, -99, -100]) := List.countP_append (p := literal q) (l₁ := [-90, -92, -93]) (l₂ := [-95, -98, -99, -100])
  have hm := merge_right (literal (valuationOf q) (1607)) (literal (valuationOf q) (1611)) (countLit q [-90, -92, -93]) (countLit q [-95, -98, -99, -100]) (count1609 q) 3 (meaning1607 q) (meaning1611 q) hs
  change valuationOf q 1607 = false ∨ valuationOf q 1611 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1247 (q : Snake 81) (h : Conditions q) : valuation q 1607 = false ∨ valuation q 1611 = true := counterClause1247 (baseVal q)

theorem counterClause1248 (q : Nat → Bool) : valuationOf q 1598 = false ∨ valuationOf q 1609 = true := by
  have hs : count1609 q = (countLit q [-90, -92, -93]) + (countLit q [-95, -98, -99, -100]) := List.countP_append (p := literal q) (l₁ := [-90, -92, -93]) (l₂ := [-95, -98, -99, -100])
  have hm := merge_left (literal (valuationOf q) (1598)) (literal (valuationOf q) (1609)) (countLit q [-90, -92, -93]) (countLit q [-95, -98, -99, -100]) (count1609 q) 1 (meaning1598 q) (meaning1609 q) hs
  change valuationOf q 1598 = false ∨ valuationOf q 1609 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1248 (q : Snake 81) (h : Conditions q) : valuation q 1598 = false ∨ valuation q 1609 = true := counterClause1248 (baseVal q)

theorem block38 (q : Snake 81) (h : Conditions q) : B112E207.Block38 (valuation q) :=
  ⟨clause1217 q h, clause1218 q h, clause1219 q h, clause1220 q h, clause1221 q h, clause1222 q h, clause1223 q h, clause1224 q h, clause1225 q h, clause1226 q h, clause1227 q h, clause1228 q h, clause1229 q h, clause1230 q h, clause1231 q h, clause1232 q h, clause1233 q h, clause1234 q h, clause1235 q h, clause1236 q h, clause1237 q h, clause1238 q h, clause1239 q h, clause1240 q h, clause1241 q h, clause1242 q h, clause1243 q h, clause1244 q h, clause1245 q h, clause1246 q h, clause1247 q h, clause1248 q h⟩

end
end Snake9.Regrowth.E112207
