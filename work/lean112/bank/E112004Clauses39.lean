import E112004Semantics
import B112E004Inputs
namespace Snake9.Regrowth.E112004
noncomputable section
local instance blockDec39 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1249 (q : Nat → Bool) : valuationOf q 1520 = false ∨ valuationOf q 1523 = false ∨ valuationOf q 1526 = true := by
  have hs : count1524 q = (countLit q [-46, -48]) + (countLit q [-51, -52]) := List.countP_append (p := literal q) (l₁ := [-46, -48]) (l₂ := [-51, -52])
  have hm := merge_two (literal (valuationOf q) (1520)) (literal (valuationOf q) (1523)) (literal (valuationOf q) (1526)) (countLit q [-46, -48]) (countLit q [-51, -52]) (count1524 q) 1 2 (meaning1520 q) (meaning1523 q) (meaning1526 q) hs
  change valuationOf q 1520 = false ∨ valuationOf q 1523 = false ∨ valuationOf q 1526 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1249 (q : Snake 81) (h : Conditions q) : valuation q 1520 = false ∨ valuation q 1523 = false ∨ valuation q 1526 = true := counterClause1249 (baseVal q)

theorem counterClause1250 (q : Nat → Bool) : valuationOf q 1521 = false ∨ valuationOf q 1525 = true := by
  have hs : count1524 q = (countLit q [-46, -48]) + (countLit q [-51, -52]) := List.countP_append (p := literal q) (l₁ := [-46, -48]) (l₂ := [-51, -52])
  have hm := merge_left (literal (valuationOf q) (1521)) (literal (valuationOf q) (1525)) (countLit q [-46, -48]) (countLit q [-51, -52]) (count1524 q) 2 (meaning1521 q) (meaning1525 q) hs
  change valuationOf q 1521 = false ∨ valuationOf q 1525 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1250 (q : Snake 81) (h : Conditions q) : valuation q 1521 = false ∨ valuation q 1525 = true := counterClause1250 (baseVal q)

theorem counterClause1251 (q : Nat → Bool) : valuationOf q 1521 = false ∨ valuationOf q 1522 = false ∨ valuationOf q 1526 = true := by
  have hs : count1524 q = (countLit q [-46, -48]) + (countLit q [-51, -52]) := List.countP_append (p := literal q) (l₁ := [-46, -48]) (l₂ := [-51, -52])
  have hm := merge_two (literal (valuationOf q) (1521)) (literal (valuationOf q) (1522)) (literal (valuationOf q) (1526)) (countLit q [-46, -48]) (countLit q [-51, -52]) (count1524 q) 2 1 (meaning1521 q) (meaning1522 q) (meaning1526 q) hs
  change valuationOf q 1521 = false ∨ valuationOf q 1522 = false ∨ valuationOf q 1526 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1251 (q : Snake 81) (h : Conditions q) : valuation q 1521 = false ∨ valuation q 1522 = false ∨ valuation q 1526 = true := counterClause1251 (baseVal q)

theorem counterClause1252 (q : Nat → Bool) : valuationOf q 1521 = false ∨ valuationOf q 1523 = false ∨ valuationOf q 1527 = true := by
  have hs : count1524 q = (countLit q [-46, -48]) + (countLit q [-51, -52]) := List.countP_append (p := literal q) (l₁ := [-46, -48]) (l₂ := [-51, -52])
  have hm := merge_two (literal (valuationOf q) (1521)) (literal (valuationOf q) (1523)) (literal (valuationOf q) (1527)) (countLit q [-46, -48]) (countLit q [-51, -52]) (count1524 q) 2 2 (meaning1521 q) (meaning1523 q) (meaning1527 q) hs
  change valuationOf q 1521 = false ∨ valuationOf q 1523 = false ∨ valuationOf q 1527 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1252 (q : Snake 81) (h : Conditions q) : valuation q 1521 = false ∨ valuation q 1523 = false ∨ valuation q 1527 = true := counterClause1252 (baseVal q)

theorem counterClause1253 (q : Nat → Bool) : valuationOf q 56 = true ∨ valuationOf q 1528 = true := by
  have hs : count1528 q = (countLit q [-53]) + (countLit q [-56]) := List.countP_append (p := literal q) (l₁ := [-53]) (l₂ := [-56])
  have hm := merge_right (literal (valuationOf q) (-56)) (literal (valuationOf q) (1528)) (countLit q [-53]) (countLit q [-56]) (count1528 q) 1 (meaningNeg56 q) (meaning1528 q) hs
  change (! (valuationOf q 56)) = false ∨ valuationOf q 1528 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1253 (q : Snake 81) (h : Conditions q) : valuation q 56 = true ∨ valuation q 1528 = true := counterClause1253 (baseVal q)

theorem counterClause1254 (q : Nat → Bool) : valuationOf q 53 = true ∨ valuationOf q 1528 = true := by
  have hs : count1528 q = (countLit q [-53]) + (countLit q [-56]) := List.countP_append (p := literal q) (l₁ := [-53]) (l₂ := [-56])
  have hm := merge_left (literal (valuationOf q) (-53)) (literal (valuationOf q) (1528)) (countLit q [-53]) (countLit q [-56]) (count1528 q) 1 (meaningNeg53 q) (meaning1528 q) hs
  change (! (valuationOf q 53)) = false ∨ valuationOf q 1528 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1254 (q : Snake 81) (h : Conditions q) : valuation q 53 = true ∨ valuation q 1528 = true := counterClause1254 (baseVal q)

theorem counterClause1255 (q : Nat → Bool) : valuationOf q 53 = true ∨ valuationOf q 56 = true ∨ valuationOf q 1529 = true := by
  have hs : count1528 q = (countLit q [-53]) + (countLit q [-56]) := List.countP_append (p := literal q) (l₁ := [-53]) (l₂ := [-56])
  have hm := merge_two (literal (valuationOf q) (-53)) (literal (valuationOf q) (-56)) (literal (valuationOf q) (1529)) (countLit q [-53]) (countLit q [-56]) (count1528 q) 1 1 (meaningNeg53 q) (meaningNeg56 q) (meaning1529 q) hs
  change (! (valuationOf q 53)) = false ∨ (! (valuationOf q 56)) = false ∨ valuationOf q 1529 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1255 (q : Snake 81) (h : Conditions q) : valuation q 53 = true ∨ valuation q 56 = true ∨ valuation q 1529 = true := counterClause1255 (baseVal q)

theorem counterClause1256 (q : Nat → Bool) : valuationOf q 60 = true ∨ valuationOf q 1530 = true := by
  have hs : count1530 q = (countLit q [-59]) + (countLit q [-60]) := List.countP_append (p := literal q) (l₁ := [-59]) (l₂ := [-60])
  have hm := merge_right (literal (valuationOf q) (-60)) (literal (valuationOf q) (1530)) (countLit q [-59]) (countLit q [-60]) (count1530 q) 1 (meaningNeg60 q) (meaning1530 q) hs
  change (! (valuationOf q 60)) = false ∨ valuationOf q 1530 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1256 (q : Snake 81) (h : Conditions q) : valuation q 60 = true ∨ valuation q 1530 = true := counterClause1256 (baseVal q)

theorem counterClause1257 (q : Nat → Bool) : valuationOf q 59 = true ∨ valuationOf q 1530 = true := by
  have hs : count1530 q = (countLit q [-59]) + (countLit q [-60]) := List.countP_append (p := literal q) (l₁ := [-59]) (l₂ := [-60])
  have hm := merge_left (literal (valuationOf q) (-59)) (literal (valuationOf q) (1530)) (countLit q [-59]) (countLit q [-60]) (count1530 q) 1 (meaningNeg59 q) (meaning1530 q) hs
  change (! (valuationOf q 59)) = false ∨ valuationOf q 1530 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1257 (q : Snake 81) (h : Conditions q) : valuation q 59 = true ∨ valuation q 1530 = true := counterClause1257 (baseVal q)

theorem counterClause1258 (q : Nat → Bool) : valuationOf q 59 = true ∨ valuationOf q 60 = true ∨ valuationOf q 1531 = true := by
  have hs : count1530 q = (countLit q [-59]) + (countLit q [-60]) := List.countP_append (p := literal q) (l₁ := [-59]) (l₂ := [-60])
  have hm := merge_two (literal (valuationOf q) (-59)) (literal (valuationOf q) (-60)) (literal (valuationOf q) (1531)) (countLit q [-59]) (countLit q [-60]) (count1530 q) 1 1 (meaningNeg59 q) (meaningNeg60 q) (meaning1531 q) hs
  change (! (valuationOf q 59)) = false ∨ (! (valuationOf q 60)) = false ∨ valuationOf q 1531 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1258 (q : Snake 81) (h : Conditions q) : valuation q 59 = true ∨ valuation q 60 = true ∨ valuation q 1531 = true := counterClause1258 (baseVal q)

theorem counterClause1259 (q : Nat → Bool) : valuationOf q 1530 = false ∨ valuationOf q 1532 = true := by
  have hs : count1532 q = (countLit q [-53, -56]) + (countLit q [-59, -60]) := List.countP_append (p := literal q) (l₁ := [-53, -56]) (l₂ := [-59, -60])
  have hm := merge_right (literal (valuationOf q) (1530)) (literal (valuationOf q) (1532)) (countLit q [-53, -56]) (countLit q [-59, -60]) (count1532 q) 1 (meaning1530 q) (meaning1532 q) hs
  change valuationOf q 1530 = false ∨ valuationOf q 1532 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1259 (q : Snake 81) (h : Conditions q) : valuation q 1530 = false ∨ valuation q 1532 = true := counterClause1259 (baseVal q)

theorem counterClause1260 (q : Nat → Bool) : valuationOf q 1531 = false ∨ valuationOf q 1533 = true := by
  have hs : count1532 q = (countLit q [-53, -56]) + (countLit q [-59, -60]) := List.countP_append (p := literal q) (l₁ := [-53, -56]) (l₂ := [-59, -60])
  have hm := merge_right (literal (valuationOf q) (1531)) (literal (valuationOf q) (1533)) (countLit q [-53, -56]) (countLit q [-59, -60]) (count1532 q) 2 (meaning1531 q) (meaning1533 q) hs
  change valuationOf q 1531 = false ∨ valuationOf q 1533 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1260 (q : Snake 81) (h : Conditions q) : valuation q 1531 = false ∨ valuation q 1533 = true := counterClause1260 (baseVal q)

theorem counterClause1261 (q : Nat → Bool) : valuationOf q 1528 = false ∨ valuationOf q 1532 = true := by
  have hs : count1532 q = (countLit q [-53, -56]) + (countLit q [-59, -60]) := List.countP_append (p := literal q) (l₁ := [-53, -56]) (l₂ := [-59, -60])
  have hm := merge_left (literal (valuationOf q) (1528)) (literal (valuationOf q) (1532)) (countLit q [-53, -56]) (countLit q [-59, -60]) (count1532 q) 1 (meaning1528 q) (meaning1532 q) hs
  change valuationOf q 1528 = false ∨ valuationOf q 1532 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1261 (q : Snake 81) (h : Conditions q) : valuation q 1528 = false ∨ valuation q 1532 = true := counterClause1261 (baseVal q)

theorem counterClause1262 (q : Nat → Bool) : valuationOf q 1528 = false ∨ valuationOf q 1530 = false ∨ valuationOf q 1533 = true := by
  have hs : count1532 q = (countLit q [-53, -56]) + (countLit q [-59, -60]) := List.countP_append (p := literal q) (l₁ := [-53, -56]) (l₂ := [-59, -60])
  have hm := merge_two (literal (valuationOf q) (1528)) (literal (valuationOf q) (1530)) (literal (valuationOf q) (1533)) (countLit q [-53, -56]) (countLit q [-59, -60]) (count1532 q) 1 1 (meaning1528 q) (meaning1530 q) (meaning1533 q) hs
  change valuationOf q 1528 = false ∨ valuationOf q 1530 = false ∨ valuationOf q 1533 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1262 (q : Snake 81) (h : Conditions q) : valuation q 1528 = false ∨ valuation q 1530 = false ∨ valuation q 1533 = true := counterClause1262 (baseVal q)

theorem counterClause1263 (q : Nat → Bool) : valuationOf q 1528 = false ∨ valuationOf q 1531 = false ∨ valuationOf q 1534 = true := by
  have hs : count1532 q = (countLit q [-53, -56]) + (countLit q [-59, -60]) := List.countP_append (p := literal q) (l₁ := [-53, -56]) (l₂ := [-59, -60])
  have hm := merge_two (literal (valuationOf q) (1528)) (literal (valuationOf q) (1531)) (literal (valuationOf q) (1534)) (countLit q [-53, -56]) (countLit q [-59, -60]) (count1532 q) 1 2 (meaning1528 q) (meaning1531 q) (meaning1534 q) hs
  change valuationOf q 1528 = false ∨ valuationOf q 1531 = false ∨ valuationOf q 1534 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1263 (q : Snake 81) (h : Conditions q) : valuation q 1528 = false ∨ valuation q 1531 = false ∨ valuation q 1534 = true := counterClause1263 (baseVal q)

theorem counterClause1264 (q : Nat → Bool) : valuationOf q 1529 = false ∨ valuationOf q 1533 = true := by
  have hs : count1532 q = (countLit q [-53, -56]) + (countLit q [-59, -60]) := List.countP_append (p := literal q) (l₁ := [-53, -56]) (l₂ := [-59, -60])
  have hm := merge_left (literal (valuationOf q) (1529)) (literal (valuationOf q) (1533)) (countLit q [-53, -56]) (countLit q [-59, -60]) (count1532 q) 2 (meaning1529 q) (meaning1533 q) hs
  change valuationOf q 1529 = false ∨ valuationOf q 1533 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1264 (q : Snake 81) (h : Conditions q) : valuation q 1529 = false ∨ valuation q 1533 = true := counterClause1264 (baseVal q)

theorem counterClause1265 (q : Nat → Bool) : valuationOf q 1529 = false ∨ valuationOf q 1530 = false ∨ valuationOf q 1534 = true := by
  have hs : count1532 q = (countLit q [-53, -56]) + (countLit q [-59, -60]) := List.countP_append (p := literal q) (l₁ := [-53, -56]) (l₂ := [-59, -60])
  have hm := merge_two (literal (valuationOf q) (1529)) (literal (valuationOf q) (1530)) (literal (valuationOf q) (1534)) (countLit q [-53, -56]) (countLit q [-59, -60]) (count1532 q) 2 1 (meaning1529 q) (meaning1530 q) (meaning1534 q) hs
  change valuationOf q 1529 = false ∨ valuationOf q 1530 = false ∨ valuationOf q 1534 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1265 (q : Snake 81) (h : Conditions q) : valuation q 1529 = false ∨ valuation q 1530 = false ∨ valuation q 1534 = true := counterClause1265 (baseVal q)

theorem counterClause1266 (q : Nat → Bool) : valuationOf q 1529 = false ∨ valuationOf q 1531 = false ∨ valuationOf q 1535 = true := by
  have hs : count1532 q = (countLit q [-53, -56]) + (countLit q [-59, -60]) := List.countP_append (p := literal q) (l₁ := [-53, -56]) (l₂ := [-59, -60])
  have hm := merge_two (literal (valuationOf q) (1529)) (literal (valuationOf q) (1531)) (literal (valuationOf q) (1535)) (countLit q [-53, -56]) (countLit q [-59, -60]) (count1532 q) 2 2 (meaning1529 q) (meaning1531 q) (meaning1535 q) hs
  change valuationOf q 1529 = false ∨ valuationOf q 1531 = false ∨ valuationOf q 1535 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1266 (q : Snake 81) (h : Conditions q) : valuation q 1529 = false ∨ valuation q 1531 = false ∨ valuation q 1535 = true := counterClause1266 (baseVal q)

theorem counterClause1267 (q : Nat → Bool) : valuationOf q 1532 = false ∨ valuationOf q 1536 = true := by
  have hs : count1536 q = (countLit q [-46, -48, -51, -52]) + (countLit q [-53, -56, -59, -60]) := List.countP_append (p := literal q) (l₁ := [-46, -48, -51, -52]) (l₂ := [-53, -56, -59, -60])
  have hm := merge_right (literal (valuationOf q) (1532)) (literal (valuationOf q) (1536)) (countLit q [-46, -48, -51, -52]) (countLit q [-53, -56, -59, -60]) (count1536 q) 1 (meaning1532 q) (meaning1536 q) hs
  change valuationOf q 1532 = false ∨ valuationOf q 1536 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1267 (q : Snake 81) (h : Conditions q) : valuation q 1532 = false ∨ valuation q 1536 = true := counterClause1267 (baseVal q)

theorem counterClause1268 (q : Nat → Bool) : valuationOf q 1533 = false ∨ valuationOf q 1537 = true := by
  have hs : count1536 q = (countLit q [-46, -48, -51, -52]) + (countLit q [-53, -56, -59, -60]) := List.countP_append (p := literal q) (l₁ := [-46, -48, -51, -52]) (l₂ := [-53, -56, -59, -60])
  have hm := merge_right (literal (valuationOf q) (1533)) (literal (valuationOf q) (1537)) (countLit q [-46, -48, -51, -52]) (countLit q [-53, -56, -59, -60]) (count1536 q) 2 (meaning1533 q) (meaning1537 q) hs
  change valuationOf q 1533 = false ∨ valuationOf q 1537 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1268 (q : Snake 81) (h : Conditions q) : valuation q 1533 = false ∨ valuation q 1537 = true := counterClause1268 (baseVal q)

theorem counterClause1269 (q : Nat → Bool) : valuationOf q 1534 = false ∨ valuationOf q 1538 = true := by
  have hs : count1536 q = (countLit q [-46, -48, -51, -52]) + (countLit q [-53, -56, -59, -60]) := List.countP_append (p := literal q) (l₁ := [-46, -48, -51, -52]) (l₂ := [-53, -56, -59, -60])
  have hm := merge_right (literal (valuationOf q) (1534)) (literal (valuationOf q) (1538)) (countLit q [-46, -48, -51, -52]) (countLit q [-53, -56, -59, -60]) (count1536 q) 3 (meaning1534 q) (meaning1538 q) hs
  change valuationOf q 1534 = false ∨ valuationOf q 1538 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1269 (q : Snake 81) (h : Conditions q) : valuation q 1534 = false ∨ valuation q 1538 = true := counterClause1269 (baseVal q)

theorem counterClause1270 (q : Nat → Bool) : valuationOf q 1535 = false ∨ valuationOf q 1539 = true := by
  have hs : count1536 q = (countLit q [-46, -48, -51, -52]) + (countLit q [-53, -56, -59, -60]) := List.countP_append (p := literal q) (l₁ := [-46, -48, -51, -52]) (l₂ := [-53, -56, -59, -60])
  have hm := merge_right (literal (valuationOf q) (1535)) (literal (valuationOf q) (1539)) (countLit q [-46, -48, -51, -52]) (countLit q [-53, -56, -59, -60]) (count1536 q) 4 (meaning1535 q) (meaning1539 q) hs
  change valuationOf q 1535 = false ∨ valuationOf q 1539 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1270 (q : Snake 81) (h : Conditions q) : valuation q 1535 = false ∨ valuation q 1539 = true := counterClause1270 (baseVal q)

theorem counterClause1271 (q : Nat → Bool) : valuationOf q 1524 = false ∨ valuationOf q 1536 = true := by
  have hs : count1536 q = (countLit q [-46, -48, -51, -52]) + (countLit q [-53, -56, -59, -60]) := List.countP_append (p := literal q) (l₁ := [-46, -48, -51, -52]) (l₂ := [-53, -56, -59, -60])
  have hm := merge_left (literal (valuationOf q) (1524)) (literal (valuationOf q) (1536)) (countLit q [-46, -48, -51, -52]) (countLit q [-53, -56, -59, -60]) (count1536 q) 1 (meaning1524 q) (meaning1536 q) hs
  change valuationOf q 1524 = false ∨ valuationOf q 1536 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1271 (q : Snake 81) (h : Conditions q) : valuation q 1524 = false ∨ valuation q 1536 = true := counterClause1271 (baseVal q)

theorem counterClause1272 (q : Nat → Bool) : valuationOf q 1524 = false ∨ valuationOf q 1532 = false ∨ valuationOf q 1537 = true := by
  have hs : count1536 q = (countLit q [-46, -48, -51, -52]) + (countLit q [-53, -56, -59, -60]) := List.countP_append (p := literal q) (l₁ := [-46, -48, -51, -52]) (l₂ := [-53, -56, -59, -60])
  have hm := merge_two (literal (valuationOf q) (1524)) (literal (valuationOf q) (1532)) (literal (valuationOf q) (1537)) (countLit q [-46, -48, -51, -52]) (countLit q [-53, -56, -59, -60]) (count1536 q) 1 1 (meaning1524 q) (meaning1532 q) (meaning1537 q) hs
  change valuationOf q 1524 = false ∨ valuationOf q 1532 = false ∨ valuationOf q 1537 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1272 (q : Snake 81) (h : Conditions q) : valuation q 1524 = false ∨ valuation q 1532 = false ∨ valuation q 1537 = true := counterClause1272 (baseVal q)

theorem counterClause1273 (q : Nat → Bool) : valuationOf q 1524 = false ∨ valuationOf q 1533 = false ∨ valuationOf q 1538 = true := by
  have hs : count1536 q = (countLit q [-46, -48, -51, -52]) + (countLit q [-53, -56, -59, -60]) := List.countP_append (p := literal q) (l₁ := [-46, -48, -51, -52]) (l₂ := [-53, -56, -59, -60])
  have hm := merge_two (literal (valuationOf q) (1524)) (literal (valuationOf q) (1533)) (literal (valuationOf q) (1538)) (countLit q [-46, -48, -51, -52]) (countLit q [-53, -56, -59, -60]) (count1536 q) 1 2 (meaning1524 q) (meaning1533 q) (meaning1538 q) hs
  change valuationOf q 1524 = false ∨ valuationOf q 1533 = false ∨ valuationOf q 1538 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1273 (q : Snake 81) (h : Conditions q) : valuation q 1524 = false ∨ valuation q 1533 = false ∨ valuation q 1538 = true := counterClause1273 (baseVal q)

theorem counterClause1274 (q : Nat → Bool) : valuationOf q 1524 = false ∨ valuationOf q 1534 = false ∨ valuationOf q 1539 = true := by
  have hs : count1536 q = (countLit q [-46, -48, -51, -52]) + (countLit q [-53, -56, -59, -60]) := List.countP_append (p := literal q) (l₁ := [-46, -48, -51, -52]) (l₂ := [-53, -56, -59, -60])
  have hm := merge_two (literal (valuationOf q) (1524)) (literal (valuationOf q) (1534)) (literal (valuationOf q) (1539)) (countLit q [-46, -48, -51, -52]) (countLit q [-53, -56, -59, -60]) (count1536 q) 1 3 (meaning1524 q) (meaning1534 q) (meaning1539 q) hs
  change valuationOf q 1524 = false ∨ valuationOf q 1534 = false ∨ valuationOf q 1539 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1274 (q : Snake 81) (h : Conditions q) : valuation q 1524 = false ∨ valuation q 1534 = false ∨ valuation q 1539 = true := counterClause1274 (baseVal q)

theorem counterClause1275 (q : Nat → Bool) : valuationOf q 1524 = false ∨ valuationOf q 1535 = false ∨ valuationOf q 1540 = true := by
  have hs : count1536 q = (countLit q [-46, -48, -51, -52]) + (countLit q [-53, -56, -59, -60]) := List.countP_append (p := literal q) (l₁ := [-46, -48, -51, -52]) (l₂ := [-53, -56, -59, -60])
  have hm := merge_two (literal (valuationOf q) (1524)) (literal (valuationOf q) (1535)) (literal (valuationOf q) (1540)) (countLit q [-46, -48, -51, -52]) (countLit q [-53, -56, -59, -60]) (count1536 q) 1 4 (meaning1524 q) (meaning1535 q) (meaning1540 q) hs
  change valuationOf q 1524 = false ∨ valuationOf q 1535 = false ∨ valuationOf q 1540 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1275 (q : Snake 81) (h : Conditions q) : valuation q 1524 = false ∨ valuation q 1535 = false ∨ valuation q 1540 = true := counterClause1275 (baseVal q)

theorem counterClause1276 (q : Nat → Bool) : valuationOf q 1525 = false ∨ valuationOf q 1537 = true := by
  have hs : count1536 q = (countLit q [-46, -48, -51, -52]) + (countLit q [-53, -56, -59, -60]) := List.countP_append (p := literal q) (l₁ := [-46, -48, -51, -52]) (l₂ := [-53, -56, -59, -60])
  have hm := merge_left (literal (valuationOf q) (1525)) (literal (valuationOf q) (1537)) (countLit q [-46, -48, -51, -52]) (countLit q [-53, -56, -59, -60]) (count1536 q) 2 (meaning1525 q) (meaning1537 q) hs
  change valuationOf q 1525 = false ∨ valuationOf q 1537 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1276 (q : Snake 81) (h : Conditions q) : valuation q 1525 = false ∨ valuation q 1537 = true := counterClause1276 (baseVal q)

theorem counterClause1277 (q : Nat → Bool) : valuationOf q 1525 = false ∨ valuationOf q 1532 = false ∨ valuationOf q 1538 = true := by
  have hs : count1536 q = (countLit q [-46, -48, -51, -52]) + (countLit q [-53, -56, -59, -60]) := List.countP_append (p := literal q) (l₁ := [-46, -48, -51, -52]) (l₂ := [-53, -56, -59, -60])
  have hm := merge_two (literal (valuationOf q) (1525)) (literal (valuationOf q) (1532)) (literal (valuationOf q) (1538)) (countLit q [-46, -48, -51, -52]) (countLit q [-53, -56, -59, -60]) (count1536 q) 2 1 (meaning1525 q) (meaning1532 q) (meaning1538 q) hs
  change valuationOf q 1525 = false ∨ valuationOf q 1532 = false ∨ valuationOf q 1538 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1277 (q : Snake 81) (h : Conditions q) : valuation q 1525 = false ∨ valuation q 1532 = false ∨ valuation q 1538 = true := counterClause1277 (baseVal q)

theorem counterClause1278 (q : Nat → Bool) : valuationOf q 1525 = false ∨ valuationOf q 1533 = false ∨ valuationOf q 1539 = true := by
  have hs : count1536 q = (countLit q [-46, -48, -51, -52]) + (countLit q [-53, -56, -59, -60]) := List.countP_append (p := literal q) (l₁ := [-46, -48, -51, -52]) (l₂ := [-53, -56, -59, -60])
  have hm := merge_two (literal (valuationOf q) (1525)) (literal (valuationOf q) (1533)) (literal (valuationOf q) (1539)) (countLit q [-46, -48, -51, -52]) (countLit q [-53, -56, -59, -60]) (count1536 q) 2 2 (meaning1525 q) (meaning1533 q) (meaning1539 q) hs
  change valuationOf q 1525 = false ∨ valuationOf q 1533 = false ∨ valuationOf q 1539 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1278 (q : Snake 81) (h : Conditions q) : valuation q 1525 = false ∨ valuation q 1533 = false ∨ valuation q 1539 = true := counterClause1278 (baseVal q)

theorem counterClause1279 (q : Nat → Bool) : valuationOf q 1525 = false ∨ valuationOf q 1534 = false ∨ valuationOf q 1540 = true := by
  have hs : count1536 q = (countLit q [-46, -48, -51, -52]) + (countLit q [-53, -56, -59, -60]) := List.countP_append (p := literal q) (l₁ := [-46, -48, -51, -52]) (l₂ := [-53, -56, -59, -60])
  have hm := merge_two (literal (valuationOf q) (1525)) (literal (valuationOf q) (1534)) (literal (valuationOf q) (1540)) (countLit q [-46, -48, -51, -52]) (countLit q [-53, -56, -59, -60]) (count1536 q) 2 3 (meaning1525 q) (meaning1534 q) (meaning1540 q) hs
  change valuationOf q 1525 = false ∨ valuationOf q 1534 = false ∨ valuationOf q 1540 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1279 (q : Snake 81) (h : Conditions q) : valuation q 1525 = false ∨ valuation q 1534 = false ∨ valuation q 1540 = true := counterClause1279 (baseVal q)

theorem counterClause1280 (q : Nat → Bool) : valuationOf q 1525 = false ∨ valuationOf q 1535 = false ∨ valuationOf q 1541 = true := by
  have hs : count1536 q = (countLit q [-46, -48, -51, -52]) + (countLit q [-53, -56, -59, -60]) := List.countP_append (p := literal q) (l₁ := [-46, -48, -51, -52]) (l₂ := [-53, -56, -59, -60])
  have hm := merge_two (literal (valuationOf q) (1525)) (literal (valuationOf q) (1535)) (literal (valuationOf q) (1541)) (countLit q [-46, -48, -51, -52]) (countLit q [-53, -56, -59, -60]) (count1536 q) 2 4 (meaning1525 q) (meaning1535 q) (meaning1541 q) hs
  change valuationOf q 1525 = false ∨ valuationOf q 1535 = false ∨ valuationOf q 1541 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1280 (q : Snake 81) (h : Conditions q) : valuation q 1525 = false ∨ valuation q 1535 = false ∨ valuation q 1541 = true := counterClause1280 (baseVal q)

theorem block39 (q : Snake 81) (h : Conditions q) : B112E004.Block39 (valuation q) :=
  ⟨clause1249 q h, clause1250 q h, clause1251 q h, clause1252 q h, clause1253 q h, clause1254 q h, clause1255 q h, clause1256 q h, clause1257 q h, clause1258 q h, clause1259 q h, clause1260 q h, clause1261 q h, clause1262 q h, clause1263 q h, clause1264 q h, clause1265 q h, clause1266 q h, clause1267 q h, clause1268 q h, clause1269 q h, clause1270 q h, clause1271 q h, clause1272 q h, clause1273 q h, clause1274 q h, clause1275 q h, clause1276 q h, clause1277 q h, clause1278 q h, clause1279 q h, clause1280 q h⟩

end
end Snake9.Regrowth.E112004
