import E112027Semantics
import B112E027Inputs
namespace Snake9.Regrowth.E112027
noncomputable section
local instance blockDec39 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1249 (q : Nat → Bool) : valuationOf q 1578 = false ∨ valuationOf q 1595 = false ∨ valuationOf q 1606 = true := by
  have hs : count1602 q = (countLit q [-59, -61, -64, -67, -68, -70, -74]) + (countLit q [-75, -76, -77, -81, -82, -85, -89]) := List.countP_append (p := literal q) (l₁ := [-59, -61, -64, -67, -68, -70, -74]) (l₂ := [-75, -76, -77, -81, -82, -85, -89])
  have hm := merge_two (literal (valuationOf q) (1578)) (literal (valuationOf q) (1595)) (literal (valuationOf q) (1606)) (countLit q [-59, -61, -64, -67, -68, -70, -74]) (countLit q [-75, -76, -77, -81, -82, -85, -89]) (count1602 q) 4 1 (meaning1578 q) (meaning1595 q) (meaning1606 q) hs
  change valuationOf q 1578 = false ∨ valuationOf q 1595 = false ∨ valuationOf q 1606 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1249 (q : Snake 81) (h : Conditions q) : valuation q 1578 = false ∨ valuation q 1595 = false ∨ valuation q 1606 = true := counterClause1249 (baseVal q)

theorem counterClause1250 (q : Nat → Bool) : valuationOf q 1578 = false ∨ valuationOf q 1596 = false ∨ valuationOf q 1607 = true := by
  have hs : count1602 q = (countLit q [-59, -61, -64, -67, -68, -70, -74]) + (countLit q [-75, -76, -77, -81, -82, -85, -89]) := List.countP_append (p := literal q) (l₁ := [-59, -61, -64, -67, -68, -70, -74]) (l₂ := [-75, -76, -77, -81, -82, -85, -89])
  have hm := merge_two (literal (valuationOf q) (1578)) (literal (valuationOf q) (1596)) (literal (valuationOf q) (1607)) (countLit q [-59, -61, -64, -67, -68, -70, -74]) (countLit q [-75, -76, -77, -81, -82, -85, -89]) (count1602 q) 4 2 (meaning1578 q) (meaning1596 q) (meaning1607 q) hs
  change valuationOf q 1578 = false ∨ valuationOf q 1596 = false ∨ valuationOf q 1607 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1250 (q : Snake 81) (h : Conditions q) : valuation q 1578 = false ∨ valuation q 1596 = false ∨ valuation q 1607 = true := counterClause1250 (baseVal q)

theorem counterClause1251 (q : Nat → Bool) : valuationOf q 1578 = false ∨ valuationOf q 1597 = false ∨ valuationOf q 1608 = true := by
  have hs : count1602 q = (countLit q [-59, -61, -64, -67, -68, -70, -74]) + (countLit q [-75, -76, -77, -81, -82, -85, -89]) := List.countP_append (p := literal q) (l₁ := [-59, -61, -64, -67, -68, -70, -74]) (l₂ := [-75, -76, -77, -81, -82, -85, -89])
  have hm := merge_two (literal (valuationOf q) (1578)) (literal (valuationOf q) (1597)) (literal (valuationOf q) (1608)) (countLit q [-59, -61, -64, -67, -68, -70, -74]) (countLit q [-75, -76, -77, -81, -82, -85, -89]) (count1602 q) 4 3 (meaning1578 q) (meaning1597 q) (meaning1608 q) hs
  change valuationOf q 1578 = false ∨ valuationOf q 1597 = false ∨ valuationOf q 1608 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1251 (q : Snake 81) (h : Conditions q) : valuation q 1578 = false ∨ valuation q 1597 = false ∨ valuation q 1608 = true := counterClause1251 (baseVal q)

theorem counterClause1252 (q : Nat → Bool) : valuationOf q 1578 = false ∨ valuationOf q 1598 = false ∨ valuationOf q 1609 = true := by
  have hs : count1602 q = (countLit q [-59, -61, -64, -67, -68, -70, -74]) + (countLit q [-75, -76, -77, -81, -82, -85, -89]) := List.countP_append (p := literal q) (l₁ := [-59, -61, -64, -67, -68, -70, -74]) (l₂ := [-75, -76, -77, -81, -82, -85, -89])
  have hm := merge_two (literal (valuationOf q) (1578)) (literal (valuationOf q) (1598)) (literal (valuationOf q) (1609)) (countLit q [-59, -61, -64, -67, -68, -70, -74]) (countLit q [-75, -76, -77, -81, -82, -85, -89]) (count1602 q) 4 4 (meaning1578 q) (meaning1598 q) (meaning1609 q) hs
  change valuationOf q 1578 = false ∨ valuationOf q 1598 = false ∨ valuationOf q 1609 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1252 (q : Snake 81) (h : Conditions q) : valuation q 1578 = false ∨ valuation q 1598 = false ∨ valuation q 1609 = true := counterClause1252 (baseVal q)

theorem counterClause1253 (q : Nat → Bool) : valuationOf q 1579 = false ∨ valuationOf q 1595 = false ∨ valuationOf q 1607 = true := by
  have hs : count1602 q = (countLit q [-59, -61, -64, -67, -68, -70, -74]) + (countLit q [-75, -76, -77, -81, -82, -85, -89]) := List.countP_append (p := literal q) (l₁ := [-59, -61, -64, -67, -68, -70, -74]) (l₂ := [-75, -76, -77, -81, -82, -85, -89])
  have hm := merge_two (literal (valuationOf q) (1579)) (literal (valuationOf q) (1595)) (literal (valuationOf q) (1607)) (countLit q [-59, -61, -64, -67, -68, -70, -74]) (countLit q [-75, -76, -77, -81, -82, -85, -89]) (count1602 q) 5 1 (meaning1579 q) (meaning1595 q) (meaning1607 q) hs
  change valuationOf q 1579 = false ∨ valuationOf q 1595 = false ∨ valuationOf q 1607 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1253 (q : Snake 81) (h : Conditions q) : valuation q 1579 = false ∨ valuation q 1595 = false ∨ valuation q 1607 = true := counterClause1253 (baseVal q)

theorem counterClause1254 (q : Nat → Bool) : valuationOf q 95 = true ∨ valuationOf q 1616 = true := by
  have hs : count1616 q = (countLit q [-92]) + (countLit q [-95]) := List.countP_append (p := literal q) (l₁ := [-92]) (l₂ := [-95])
  have hm := merge_right (literal (valuationOf q) (-95)) (literal (valuationOf q) (1616)) (countLit q [-92]) (countLit q [-95]) (count1616 q) 1 (meaningNeg95 q) (meaning1616 q) hs
  change (! (valuationOf q 95)) = false ∨ valuationOf q 1616 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1254 (q : Snake 81) (h : Conditions q) : valuation q 95 = true ∨ valuation q 1616 = true := counterClause1254 (baseVal q)

theorem counterClause1255 (q : Nat → Bool) : valuationOf q 92 = true ∨ valuationOf q 1616 = true := by
  have hs : count1616 q = (countLit q [-92]) + (countLit q [-95]) := List.countP_append (p := literal q) (l₁ := [-92]) (l₂ := [-95])
  have hm := merge_left (literal (valuationOf q) (-92)) (literal (valuationOf q) (1616)) (countLit q [-92]) (countLit q [-95]) (count1616 q) 1 (meaningNeg92 q) (meaning1616 q) hs
  change (! (valuationOf q 92)) = false ∨ valuationOf q 1616 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1255 (q : Snake 81) (h : Conditions q) : valuation q 92 = true ∨ valuation q 1616 = true := counterClause1255 (baseVal q)

theorem counterClause1256 (q : Nat → Bool) : valuationOf q 92 = true ∨ valuationOf q 95 = true ∨ valuationOf q 1617 = true := by
  have hs : count1616 q = (countLit q [-92]) + (countLit q [-95]) := List.countP_append (p := literal q) (l₁ := [-92]) (l₂ := [-95])
  have hm := merge_two (literal (valuationOf q) (-92)) (literal (valuationOf q) (-95)) (literal (valuationOf q) (1617)) (countLit q [-92]) (countLit q [-95]) (count1616 q) 1 1 (meaningNeg92 q) (meaningNeg95 q) (meaning1617 q) hs
  change (! (valuationOf q 92)) = false ∨ (! (valuationOf q 95)) = false ∨ valuationOf q 1617 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1256 (q : Snake 81) (h : Conditions q) : valuation q 92 = true ∨ valuation q 95 = true ∨ valuation q 1617 = true := counterClause1256 (baseVal q)

theorem counterClause1257 (q : Nat → Bool) : valuationOf q 1616 = false ∨ valuationOf q 1618 = true := by
  have hs : count1618 q = (countLit q [-90]) + (countLit q [-92, -95]) := List.countP_append (p := literal q) (l₁ := [-90]) (l₂ := [-92, -95])
  have hm := merge_right (literal (valuationOf q) (1616)) (literal (valuationOf q) (1618)) (countLit q [-90]) (countLit q [-92, -95]) (count1618 q) 1 (meaning1616 q) (meaning1618 q) hs
  change valuationOf q 1616 = false ∨ valuationOf q 1618 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1257 (q : Snake 81) (h : Conditions q) : valuation q 1616 = false ∨ valuation q 1618 = true := counterClause1257 (baseVal q)

theorem counterClause1258 (q : Nat → Bool) : valuationOf q 1617 = false ∨ valuationOf q 1619 = true := by
  have hs : count1618 q = (countLit q [-90]) + (countLit q [-92, -95]) := List.countP_append (p := literal q) (l₁ := [-90]) (l₂ := [-92, -95])
  have hm := merge_right (literal (valuationOf q) (1617)) (literal (valuationOf q) (1619)) (countLit q [-90]) (countLit q [-92, -95]) (count1618 q) 2 (meaning1617 q) (meaning1619 q) hs
  change valuationOf q 1617 = false ∨ valuationOf q 1619 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1258 (q : Snake 81) (h : Conditions q) : valuation q 1617 = false ∨ valuation q 1619 = true := counterClause1258 (baseVal q)

theorem counterClause1259 (q : Nat → Bool) : valuationOf q 90 = true ∨ valuationOf q 1618 = true := by
  have hs : count1618 q = (countLit q [-90]) + (countLit q [-92, -95]) := List.countP_append (p := literal q) (l₁ := [-90]) (l₂ := [-92, -95])
  have hm := merge_left (literal (valuationOf q) (-90)) (literal (valuationOf q) (1618)) (countLit q [-90]) (countLit q [-92, -95]) (count1618 q) 1 (meaningNeg90 q) (meaning1618 q) hs
  change (! (valuationOf q 90)) = false ∨ valuationOf q 1618 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1259 (q : Snake 81) (h : Conditions q) : valuation q 90 = true ∨ valuation q 1618 = true := counterClause1259 (baseVal q)

theorem counterClause1260 (q : Nat → Bool) : valuationOf q 90 = true ∨ valuationOf q 1616 = false ∨ valuationOf q 1619 = true := by
  have hs : count1618 q = (countLit q [-90]) + (countLit q [-92, -95]) := List.countP_append (p := literal q) (l₁ := [-90]) (l₂ := [-92, -95])
  have hm := merge_two (literal (valuationOf q) (-90)) (literal (valuationOf q) (1616)) (literal (valuationOf q) (1619)) (countLit q [-90]) (countLit q [-92, -95]) (count1618 q) 1 1 (meaningNeg90 q) (meaning1616 q) (meaning1619 q) hs
  change (! (valuationOf q 90)) = false ∨ valuationOf q 1616 = false ∨ valuationOf q 1619 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1260 (q : Snake 81) (h : Conditions q) : valuation q 90 = true ∨ valuation q 1616 = false ∨ valuation q 1619 = true := counterClause1260 (baseVal q)

theorem counterClause1261 (q : Nat → Bool) : valuationOf q 90 = true ∨ valuationOf q 1617 = false ∨ valuationOf q 1620 = true := by
  have hs : count1618 q = (countLit q [-90]) + (countLit q [-92, -95]) := List.countP_append (p := literal q) (l₁ := [-90]) (l₂ := [-92, -95])
  have hm := merge_two (literal (valuationOf q) (-90)) (literal (valuationOf q) (1617)) (literal (valuationOf q) (1620)) (countLit q [-90]) (countLit q [-92, -95]) (count1618 q) 1 2 (meaningNeg90 q) (meaning1617 q) (meaning1620 q) hs
  change (! (valuationOf q 90)) = false ∨ valuationOf q 1617 = false ∨ valuationOf q 1620 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1261 (q : Snake 81) (h : Conditions q) : valuation q 90 = true ∨ valuation q 1617 = false ∨ valuation q 1620 = true := counterClause1261 (baseVal q)

theorem counterClause1262 (q : Nat → Bool) : valuationOf q 97 = true ∨ valuationOf q 1621 = true := by
  have hs : count1621 q = (countLit q [-96]) + (countLit q [-97]) := List.countP_append (p := literal q) (l₁ := [-96]) (l₂ := [-97])
  have hm := merge_right (literal (valuationOf q) (-97)) (literal (valuationOf q) (1621)) (countLit q [-96]) (countLit q [-97]) (count1621 q) 1 (meaningNeg97 q) (meaning1621 q) hs
  change (! (valuationOf q 97)) = false ∨ valuationOf q 1621 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1262 (q : Snake 81) (h : Conditions q) : valuation q 97 = true ∨ valuation q 1621 = true := counterClause1262 (baseVal q)

theorem counterClause1263 (q : Nat → Bool) : valuationOf q 96 = true ∨ valuationOf q 1621 = true := by
  have hs : count1621 q = (countLit q [-96]) + (countLit q [-97]) := List.countP_append (p := literal q) (l₁ := [-96]) (l₂ := [-97])
  have hm := merge_left (literal (valuationOf q) (-96)) (literal (valuationOf q) (1621)) (countLit q [-96]) (countLit q [-97]) (count1621 q) 1 (meaningNeg96 q) (meaning1621 q) hs
  change (! (valuationOf q 96)) = false ∨ valuationOf q 1621 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1263 (q : Snake 81) (h : Conditions q) : valuation q 96 = true ∨ valuation q 1621 = true := counterClause1263 (baseVal q)

theorem counterClause1264 (q : Nat → Bool) : valuationOf q 96 = true ∨ valuationOf q 97 = true ∨ valuationOf q 1622 = true := by
  have hs : count1621 q = (countLit q [-96]) + (countLit q [-97]) := List.countP_append (p := literal q) (l₁ := [-96]) (l₂ := [-97])
  have hm := merge_two (literal (valuationOf q) (-96)) (literal (valuationOf q) (-97)) (literal (valuationOf q) (1622)) (countLit q [-96]) (countLit q [-97]) (count1621 q) 1 1 (meaningNeg96 q) (meaningNeg97 q) (meaning1622 q) hs
  change (! (valuationOf q 96)) = false ∨ (! (valuationOf q 97)) = false ∨ valuationOf q 1622 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1264 (q : Snake 81) (h : Conditions q) : valuation q 96 = true ∨ valuation q 97 = true ∨ valuation q 1622 = true := counterClause1264 (baseVal q)

theorem counterClause1265 (q : Nat → Bool) : valuationOf q 102 = true ∨ valuationOf q 1623 = true := by
  have hs : count1623 q = (countLit q [-98]) + (countLit q [-102]) := List.countP_append (p := literal q) (l₁ := [-98]) (l₂ := [-102])
  have hm := merge_right (literal (valuationOf q) (-102)) (literal (valuationOf q) (1623)) (countLit q [-98]) (countLit q [-102]) (count1623 q) 1 (meaningNeg102 q) (meaning1623 q) hs
  change (! (valuationOf q 102)) = false ∨ valuationOf q 1623 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1265 (q : Snake 81) (h : Conditions q) : valuation q 102 = true ∨ valuation q 1623 = true := counterClause1265 (baseVal q)

theorem counterClause1266 (q : Nat → Bool) : valuationOf q 98 = true ∨ valuationOf q 1623 = true := by
  have hs : count1623 q = (countLit q [-98]) + (countLit q [-102]) := List.countP_append (p := literal q) (l₁ := [-98]) (l₂ := [-102])
  have hm := merge_left (literal (valuationOf q) (-98)) (literal (valuationOf q) (1623)) (countLit q [-98]) (countLit q [-102]) (count1623 q) 1 (meaningNeg98 q) (meaning1623 q) hs
  change (! (valuationOf q 98)) = false ∨ valuationOf q 1623 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1266 (q : Snake 81) (h : Conditions q) : valuation q 98 = true ∨ valuation q 1623 = true := counterClause1266 (baseVal q)

theorem counterClause1267 (q : Nat → Bool) : valuationOf q 98 = true ∨ valuationOf q 102 = true ∨ valuationOf q 1624 = true := by
  have hs : count1623 q = (countLit q [-98]) + (countLit q [-102]) := List.countP_append (p := literal q) (l₁ := [-98]) (l₂ := [-102])
  have hm := merge_two (literal (valuationOf q) (-98)) (literal (valuationOf q) (-102)) (literal (valuationOf q) (1624)) (countLit q [-98]) (countLit q [-102]) (count1623 q) 1 1 (meaningNeg98 q) (meaningNeg102 q) (meaning1624 q) hs
  change (! (valuationOf q 98)) = false ∨ (! (valuationOf q 102)) = false ∨ valuationOf q 1624 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1267 (q : Snake 81) (h : Conditions q) : valuation q 98 = true ∨ valuation q 102 = true ∨ valuation q 1624 = true := counterClause1267 (baseVal q)

theorem counterClause1268 (q : Nat → Bool) : valuationOf q 1623 = false ∨ valuationOf q 1625 = true := by
  have hs : count1625 q = (countLit q [-96, -97]) + (countLit q [-98, -102]) := List.countP_append (p := literal q) (l₁ := [-96, -97]) (l₂ := [-98, -102])
  have hm := merge_right (literal (valuationOf q) (1623)) (literal (valuationOf q) (1625)) (countLit q [-96, -97]) (countLit q [-98, -102]) (count1625 q) 1 (meaning1623 q) (meaning1625 q) hs
  change valuationOf q 1623 = false ∨ valuationOf q 1625 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1268 (q : Snake 81) (h : Conditions q) : valuation q 1623 = false ∨ valuation q 1625 = true := counterClause1268 (baseVal q)

theorem counterClause1269 (q : Nat → Bool) : valuationOf q 1624 = false ∨ valuationOf q 1626 = true := by
  have hs : count1625 q = (countLit q [-96, -97]) + (countLit q [-98, -102]) := List.countP_append (p := literal q) (l₁ := [-96, -97]) (l₂ := [-98, -102])
  have hm := merge_right (literal (valuationOf q) (1624)) (literal (valuationOf q) (1626)) (countLit q [-96, -97]) (countLit q [-98, -102]) (count1625 q) 2 (meaning1624 q) (meaning1626 q) hs
  change valuationOf q 1624 = false ∨ valuationOf q 1626 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1269 (q : Snake 81) (h : Conditions q) : valuation q 1624 = false ∨ valuation q 1626 = true := counterClause1269 (baseVal q)

theorem counterClause1270 (q : Nat → Bool) : valuationOf q 1621 = false ∨ valuationOf q 1625 = true := by
  have hs : count1625 q = (countLit q [-96, -97]) + (countLit q [-98, -102]) := List.countP_append (p := literal q) (l₁ := [-96, -97]) (l₂ := [-98, -102])
  have hm := merge_left (literal (valuationOf q) (1621)) (literal (valuationOf q) (1625)) (countLit q [-96, -97]) (countLit q [-98, -102]) (count1625 q) 1 (meaning1621 q) (meaning1625 q) hs
  change valuationOf q 1621 = false ∨ valuationOf q 1625 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1270 (q : Snake 81) (h : Conditions q) : valuation q 1621 = false ∨ valuation q 1625 = true := counterClause1270 (baseVal q)

theorem counterClause1271 (q : Nat → Bool) : valuationOf q 1621 = false ∨ valuationOf q 1623 = false ∨ valuationOf q 1626 = true := by
  have hs : count1625 q = (countLit q [-96, -97]) + (countLit q [-98, -102]) := List.countP_append (p := literal q) (l₁ := [-96, -97]) (l₂ := [-98, -102])
  have hm := merge_two (literal (valuationOf q) (1621)) (literal (valuationOf q) (1623)) (literal (valuationOf q) (1626)) (countLit q [-96, -97]) (countLit q [-98, -102]) (count1625 q) 1 1 (meaning1621 q) (meaning1623 q) (meaning1626 q) hs
  change valuationOf q 1621 = false ∨ valuationOf q 1623 = false ∨ valuationOf q 1626 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1271 (q : Snake 81) (h : Conditions q) : valuation q 1621 = false ∨ valuation q 1623 = false ∨ valuation q 1626 = true := counterClause1271 (baseVal q)

theorem counterClause1272 (q : Nat → Bool) : valuationOf q 1621 = false ∨ valuationOf q 1624 = false ∨ valuationOf q 1627 = true := by
  have hs : count1625 q = (countLit q [-96, -97]) + (countLit q [-98, -102]) := List.countP_append (p := literal q) (l₁ := [-96, -97]) (l₂ := [-98, -102])
  have hm := merge_two (literal (valuationOf q) (1621)) (literal (valuationOf q) (1624)) (literal (valuationOf q) (1627)) (countLit q [-96, -97]) (countLit q [-98, -102]) (count1625 q) 1 2 (meaning1621 q) (meaning1624 q) (meaning1627 q) hs
  change valuationOf q 1621 = false ∨ valuationOf q 1624 = false ∨ valuationOf q 1627 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1272 (q : Snake 81) (h : Conditions q) : valuation q 1621 = false ∨ valuation q 1624 = false ∨ valuation q 1627 = true := counterClause1272 (baseVal q)

theorem counterClause1273 (q : Nat → Bool) : valuationOf q 1622 = false ∨ valuationOf q 1626 = true := by
  have hs : count1625 q = (countLit q [-96, -97]) + (countLit q [-98, -102]) := List.countP_append (p := literal q) (l₁ := [-96, -97]) (l₂ := [-98, -102])
  have hm := merge_left (literal (valuationOf q) (1622)) (literal (valuationOf q) (1626)) (countLit q [-96, -97]) (countLit q [-98, -102]) (count1625 q) 2 (meaning1622 q) (meaning1626 q) hs
  change valuationOf q 1622 = false ∨ valuationOf q 1626 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1273 (q : Snake 81) (h : Conditions q) : valuation q 1622 = false ∨ valuation q 1626 = true := counterClause1273 (baseVal q)

theorem counterClause1274 (q : Nat → Bool) : valuationOf q 1622 = false ∨ valuationOf q 1623 = false ∨ valuationOf q 1627 = true := by
  have hs : count1625 q = (countLit q [-96, -97]) + (countLit q [-98, -102]) := List.countP_append (p := literal q) (l₁ := [-96, -97]) (l₂ := [-98, -102])
  have hm := merge_two (literal (valuationOf q) (1622)) (literal (valuationOf q) (1623)) (literal (valuationOf q) (1627)) (countLit q [-96, -97]) (countLit q [-98, -102]) (count1625 q) 2 1 (meaning1622 q) (meaning1623 q) (meaning1627 q) hs
  change valuationOf q 1622 = false ∨ valuationOf q 1623 = false ∨ valuationOf q 1627 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1274 (q : Snake 81) (h : Conditions q) : valuation q 1622 = false ∨ valuation q 1623 = false ∨ valuation q 1627 = true := counterClause1274 (baseVal q)

theorem counterClause1275 (q : Nat → Bool) : valuationOf q 1622 = false ∨ valuationOf q 1624 = false ∨ valuationOf q 1628 = true := by
  have hs : count1625 q = (countLit q [-96, -97]) + (countLit q [-98, -102]) := List.countP_append (p := literal q) (l₁ := [-96, -97]) (l₂ := [-98, -102])
  have hm := merge_two (literal (valuationOf q) (1622)) (literal (valuationOf q) (1624)) (literal (valuationOf q) (1628)) (countLit q [-96, -97]) (countLit q [-98, -102]) (count1625 q) 2 2 (meaning1622 q) (meaning1624 q) (meaning1628 q) hs
  change valuationOf q 1622 = false ∨ valuationOf q 1624 = false ∨ valuationOf q 1628 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1275 (q : Snake 81) (h : Conditions q) : valuation q 1622 = false ∨ valuation q 1624 = false ∨ valuation q 1628 = true := counterClause1275 (baseVal q)

theorem counterClause1276 (q : Nat → Bool) : valuationOf q 1625 = false ∨ valuationOf q 1629 = true := by
  have hs : count1629 q = (countLit q [-90, -92, -95]) + (countLit q [-96, -97, -98, -102]) := List.countP_append (p := literal q) (l₁ := [-90, -92, -95]) (l₂ := [-96, -97, -98, -102])
  have hm := merge_right (literal (valuationOf q) (1625)) (literal (valuationOf q) (1629)) (countLit q [-90, -92, -95]) (countLit q [-96, -97, -98, -102]) (count1629 q) 1 (meaning1625 q) (meaning1629 q) hs
  change valuationOf q 1625 = false ∨ valuationOf q 1629 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1276 (q : Snake 81) (h : Conditions q) : valuation q 1625 = false ∨ valuation q 1629 = true := counterClause1276 (baseVal q)

theorem counterClause1277 (q : Nat → Bool) : valuationOf q 1626 = false ∨ valuationOf q 1630 = true := by
  have hs : count1629 q = (countLit q [-90, -92, -95]) + (countLit q [-96, -97, -98, -102]) := List.countP_append (p := literal q) (l₁ := [-90, -92, -95]) (l₂ := [-96, -97, -98, -102])
  have hm := merge_right (literal (valuationOf q) (1626)) (literal (valuationOf q) (1630)) (countLit q [-90, -92, -95]) (countLit q [-96, -97, -98, -102]) (count1629 q) 2 (meaning1626 q) (meaning1630 q) hs
  change valuationOf q 1626 = false ∨ valuationOf q 1630 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1277 (q : Snake 81) (h : Conditions q) : valuation q 1626 = false ∨ valuation q 1630 = true := counterClause1277 (baseVal q)

theorem counterClause1278 (q : Nat → Bool) : valuationOf q 1627 = false ∨ valuationOf q 1631 = true := by
  have hs : count1629 q = (countLit q [-90, -92, -95]) + (countLit q [-96, -97, -98, -102]) := List.countP_append (p := literal q) (l₁ := [-90, -92, -95]) (l₂ := [-96, -97, -98, -102])
  have hm := merge_right (literal (valuationOf q) (1627)) (literal (valuationOf q) (1631)) (countLit q [-90, -92, -95]) (countLit q [-96, -97, -98, -102]) (count1629 q) 3 (meaning1627 q) (meaning1631 q) hs
  change valuationOf q 1627 = false ∨ valuationOf q 1631 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1278 (q : Snake 81) (h : Conditions q) : valuation q 1627 = false ∨ valuation q 1631 = true := counterClause1278 (baseVal q)

theorem counterClause1279 (q : Nat → Bool) : valuationOf q 1628 = false ∨ valuationOf q 1632 = true := by
  have hs : count1629 q = (countLit q [-90, -92, -95]) + (countLit q [-96, -97, -98, -102]) := List.countP_append (p := literal q) (l₁ := [-90, -92, -95]) (l₂ := [-96, -97, -98, -102])
  have hm := merge_right (literal (valuationOf q) (1628)) (literal (valuationOf q) (1632)) (countLit q [-90, -92, -95]) (countLit q [-96, -97, -98, -102]) (count1629 q) 4 (meaning1628 q) (meaning1632 q) hs
  change valuationOf q 1628 = false ∨ valuationOf q 1632 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1279 (q : Snake 81) (h : Conditions q) : valuation q 1628 = false ∨ valuation q 1632 = true := counterClause1279 (baseVal q)

theorem counterClause1280 (q : Nat → Bool) : valuationOf q 1618 = false ∨ valuationOf q 1629 = true := by
  have hs : count1629 q = (countLit q [-90, -92, -95]) + (countLit q [-96, -97, -98, -102]) := List.countP_append (p := literal q) (l₁ := [-90, -92, -95]) (l₂ := [-96, -97, -98, -102])
  have hm := merge_left (literal (valuationOf q) (1618)) (literal (valuationOf q) (1629)) (countLit q [-90, -92, -95]) (countLit q [-96, -97, -98, -102]) (count1629 q) 1 (meaning1618 q) (meaning1629 q) hs
  change valuationOf q 1618 = false ∨ valuationOf q 1629 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1280 (q : Snake 81) (h : Conditions q) : valuation q 1618 = false ∨ valuation q 1629 = true := counterClause1280 (baseVal q)

theorem block39 (q : Snake 81) (h : Conditions q) : B112E027.Block39 (valuation q) :=
  ⟨clause1249 q h, clause1250 q h, clause1251 q h, clause1252 q h, clause1253 q h, clause1254 q h, clause1255 q h, clause1256 q h, clause1257 q h, clause1258 q h, clause1259 q h, clause1260 q h, clause1261 q h, clause1262 q h, clause1263 q h, clause1264 q h, clause1265 q h, clause1266 q h, clause1267 q h, clause1268 q h, clause1269 q h, clause1270 q h, clause1271 q h, clause1272 q h, clause1273 q h, clause1274 q h, clause1275 q h, clause1276 q h, clause1277 q h, clause1278 q h, clause1279 q h, clause1280 q h⟩

end
end Snake9.Regrowth.E112027
