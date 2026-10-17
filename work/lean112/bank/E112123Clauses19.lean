import E112123Semantics
import B112E123Inputs
namespace Snake9.Regrowth.E112123
noncomputable section
local instance blockDec19 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause609 (q : Nat → Bool) : valuationOf q 1327 = false ∨ valuationOf q 1332 = false ∨ valuationOf q 1336 = true := by
  have hs : count1335 q = (countLit q [-2, -3, -7]) + (countLit q [-8, -10, -13]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -7]) (l₂ := [-8, -10, -13])
  have hm := merge_two (literal (valuationOf q) (1327)) (literal (valuationOf q) (1332)) (literal (valuationOf q) (1336)) (countLit q [-2, -3, -7]) (countLit q [-8, -10, -13]) (count1335 q) 1 1 (meaning1327 q) (meaning1332 q) (meaning1336 q) hs
  change valuationOf q 1327 = false ∨ valuationOf q 1332 = false ∨ valuationOf q 1336 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause609 (q : Snake 81) (h : Conditions q) : valuation q 1327 = false ∨ valuation q 1332 = false ∨ valuation q 1336 = true := counterClause609 (baseVal q)

theorem counterClause610 (q : Nat → Bool) : valuationOf q 19 = true ∨ valuationOf q 1341 = true := by
  have hs : count1341 q = (countLit q [-16]) + (countLit q [-19]) := List.countP_append (p := literal q) (l₁ := [-16]) (l₂ := [-19])
  have hm := merge_right (literal (valuationOf q) (-19)) (literal (valuationOf q) (1341)) (countLit q [-16]) (countLit q [-19]) (count1341 q) 1 (meaningNeg19 q) (meaning1341 q) hs
  change (! (valuationOf q 19)) = false ∨ valuationOf q 1341 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause610 (q : Snake 81) (h : Conditions q) : valuation q 19 = true ∨ valuation q 1341 = true := counterClause610 (baseVal q)

theorem counterClause611 (q : Nat → Bool) : valuationOf q 16 = true ∨ valuationOf q 1341 = true := by
  have hs : count1341 q = (countLit q [-16]) + (countLit q [-19]) := List.countP_append (p := literal q) (l₁ := [-16]) (l₂ := [-19])
  have hm := merge_left (literal (valuationOf q) (-16)) (literal (valuationOf q) (1341)) (countLit q [-16]) (countLit q [-19]) (count1341 q) 1 (meaningNeg16 q) (meaning1341 q) hs
  change (! (valuationOf q 16)) = false ∨ valuationOf q 1341 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause611 (q : Snake 81) (h : Conditions q) : valuation q 16 = true ∨ valuation q 1341 = true := counterClause611 (baseVal q)

theorem counterClause612 (q : Nat → Bool) : valuationOf q 14 = true ∨ valuationOf q 1341 = false ∨ valuationOf q 1344 = true := by
  have hs : count1343 q = (countLit q [-14]) + (countLit q [-16, -19]) := List.countP_append (p := literal q) (l₁ := [-14]) (l₂ := [-16, -19])
  have hm := merge_two (literal (valuationOf q) (-14)) (literal (valuationOf q) (1341)) (literal (valuationOf q) (1344)) (countLit q [-14]) (countLit q [-16, -19]) (count1343 q) 1 1 (meaningNeg14 q) (meaning1341 q) (meaning1344 q) hs
  change (! (valuationOf q 14)) = false ∨ valuationOf q 1341 = false ∨ valuationOf q 1344 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause612 (q : Snake 81) (h : Conditions q) : valuation q 14 = true ∨ valuation q 1341 = false ∨ valuation q 1344 = true := counterClause612 (baseVal q)

theorem counterClause613 (q : Nat → Bool) : valuationOf q 22 = true ∨ valuationOf q 1346 = true := by
  have hs : count1346 q = (countLit q [-22]) + (countLit q [-23]) := List.countP_append (p := literal q) (l₁ := [-22]) (l₂ := [-23])
  have hm := merge_left (literal (valuationOf q) (-22)) (literal (valuationOf q) (1346)) (countLit q [-22]) (countLit q [-23]) (count1346 q) 1 (meaningNeg22 q) (meaning1346 q) hs
  change (! (valuationOf q 22)) = false ∨ valuationOf q 1346 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause613 (q : Snake 81) (h : Conditions q) : valuation q 22 = true ∨ valuation q 1346 = true := counterClause613 (baseVal q)

theorem counterClause614 (q : Nat → Bool) : valuationOf q 26 = true ∨ valuationOf q 1348 = true := by
  have hs : count1348 q = (countLit q [-26]) + (countLit q [-28]) := List.countP_append (p := literal q) (l₁ := [-26]) (l₂ := [-28])
  have hm := merge_left (literal (valuationOf q) (-26)) (literal (valuationOf q) (1348)) (countLit q [-26]) (countLit q [-28]) (count1348 q) 1 (meaningNeg26 q) (meaning1348 q) hs
  change (! (valuationOf q 26)) = false ∨ valuationOf q 1348 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause614 (q : Snake 81) (h : Conditions q) : valuation q 26 = true ∨ valuation q 1348 = true := counterClause614 (baseVal q)

theorem counterClause615 (q : Nat → Bool) : valuationOf q 1348 = false ∨ valuationOf q 1350 = true := by
  have hs : count1350 q = (countLit q [-22, -23]) + (countLit q [-26, -28]) := List.countP_append (p := literal q) (l₁ := [-22, -23]) (l₂ := [-26, -28])
  have hm := merge_right (literal (valuationOf q) (1348)) (literal (valuationOf q) (1350)) (countLit q [-22, -23]) (countLit q [-26, -28]) (count1350 q) 1 (meaning1348 q) (meaning1350 q) hs
  change valuationOf q 1348 = false ∨ valuationOf q 1350 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause615 (q : Snake 81) (h : Conditions q) : valuation q 1348 = false ∨ valuation q 1350 = true := counterClause615 (baseVal q)

theorem counterClause616 (q : Nat → Bool) : valuationOf q 1346 = false ∨ valuationOf q 1350 = true := by
  have hs : count1350 q = (countLit q [-22, -23]) + (countLit q [-26, -28]) := List.countP_append (p := literal q) (l₁ := [-22, -23]) (l₂ := [-26, -28])
  have hm := merge_left (literal (valuationOf q) (1346)) (literal (valuationOf q) (1350)) (countLit q [-22, -23]) (countLit q [-26, -28]) (count1350 q) 1 (meaning1346 q) (meaning1350 q) hs
  change valuationOf q 1346 = false ∨ valuationOf q 1350 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause616 (q : Snake 81) (h : Conditions q) : valuation q 1346 = false ∨ valuation q 1350 = true := counterClause616 (baseVal q)

theorem counterClause617 (q : Nat → Bool) : valuationOf q 1344 = false ∨ valuationOf q 1350 = false ∨ valuationOf q 1356 = true := by
  have hs : count1354 q = (countLit q [-14, -16, -19]) + (countLit q [-22, -23, -26, -28]) := List.countP_append (p := literal q) (l₁ := [-14, -16, -19]) (l₂ := [-22, -23, -26, -28])
  have hm := merge_two (literal (valuationOf q) (1344)) (literal (valuationOf q) (1350)) (literal (valuationOf q) (1356)) (countLit q [-14, -16, -19]) (countLit q [-22, -23, -26, -28]) (count1354 q) 2 1 (meaning1344 q) (meaning1350 q) (meaning1356 q) hs
  change valuationOf q 1344 = false ∨ valuationOf q 1350 = false ∨ valuationOf q 1356 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause617 (q : Snake 81) (h : Conditions q) : valuation q 1344 = false ∨ valuation q 1350 = false ∨ valuation q 1356 = true := counterClause617 (baseVal q)

theorem counterClause618 (q : Nat → Bool) : valuationOf q 1335 = false ∨ valuationOf q 1356 = false ∨ valuationOf q 1364 = true := by
  have hs : count1361 q = (countLit q [-2, -3, -7, -8, -10, -13]) + (countLit q [-14, -16, -19, -22, -23, -26, -28]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -7, -8, -10, -13]) (l₂ := [-14, -16, -19, -22, -23, -26, -28])
  have hm := merge_two (literal (valuationOf q) (1335)) (literal (valuationOf q) (1356)) (literal (valuationOf q) (1364)) (countLit q [-2, -3, -7, -8, -10, -13]) (countLit q [-14, -16, -19, -22, -23, -26, -28]) (count1361 q) 1 3 (meaning1335 q) (meaning1356 q) (meaning1364 q) hs
  change valuationOf q 1335 = false ∨ valuationOf q 1356 = false ∨ valuationOf q 1364 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause618 (q : Snake 81) (h : Conditions q) : valuation q 1335 = false ∨ valuation q 1356 = false ∨ valuation q 1364 = true := counterClause618 (baseVal q)

theorem counterClause619 (q : Nat → Bool) : valuationOf q 1336 = false ∨ valuationOf q 1356 = false ∨ valuationOf q 1365 = true := by
  have hs : count1361 q = (countLit q [-2, -3, -7, -8, -10, -13]) + (countLit q [-14, -16, -19, -22, -23, -26, -28]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -7, -8, -10, -13]) (l₂ := [-14, -16, -19, -22, -23, -26, -28])
  have hm := merge_two (literal (valuationOf q) (1336)) (literal (valuationOf q) (1356)) (literal (valuationOf q) (1365)) (countLit q [-2, -3, -7, -8, -10, -13]) (countLit q [-14, -16, -19, -22, -23, -26, -28]) (count1361 q) 2 3 (meaning1336 q) (meaning1356 q) (meaning1365 q) hs
  change valuationOf q 1336 = false ∨ valuationOf q 1356 = false ∨ valuationOf q 1365 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause619 (q : Snake 81) (h : Conditions q) : valuation q 1336 = false ∨ valuation q 1356 = false ∨ valuation q 1365 = true := counterClause619 (baseVal q)

theorem counterClause620 (q : Nat → Bool) : valuationOf q 35 = true ∨ valuationOf q 1374 = true := by
  have hs : count1374 q = (countLit q [-34]) + (countLit q [-35]) := List.countP_append (p := literal q) (l₁ := [-34]) (l₂ := [-35])
  have hm := merge_right (literal (valuationOf q) (-35)) (literal (valuationOf q) (1374)) (countLit q [-34]) (countLit q [-35]) (count1374 q) 1 (meaningNeg35 q) (meaning1374 q) hs
  change (! (valuationOf q 35)) = false ∨ valuationOf q 1374 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause620 (q : Snake 81) (h : Conditions q) : valuation q 35 = true ∨ valuation q 1374 = true := counterClause620 (baseVal q)

theorem counterClause621 (q : Nat → Bool) : valuationOf q 34 = true ∨ valuationOf q 1374 = true := by
  have hs : count1374 q = (countLit q [-34]) + (countLit q [-35]) := List.countP_append (p := literal q) (l₁ := [-34]) (l₂ := [-35])
  have hm := merge_left (literal (valuationOf q) (-34)) (literal (valuationOf q) (1374)) (countLit q [-34]) (countLit q [-35]) (count1374 q) 1 (meaningNeg34 q) (meaning1374 q) hs
  change (! (valuationOf q 34)) = false ∨ valuationOf q 1374 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause621 (q : Snake 81) (h : Conditions q) : valuation q 34 = true ∨ valuation q 1374 = true := counterClause621 (baseVal q)

theorem counterClause622 (q : Nat → Bool) : valuationOf q 1374 = false ∨ valuationOf q 1376 = true := by
  have hs : count1376 q = (countLit q [-31]) + (countLit q [-34, -35]) := List.countP_append (p := literal q) (l₁ := [-31]) (l₂ := [-34, -35])
  have hm := merge_right (literal (valuationOf q) (1374)) (literal (valuationOf q) (1376)) (countLit q [-31]) (countLit q [-34, -35]) (count1376 q) 1 (meaning1374 q) (meaning1376 q) hs
  change valuationOf q 1374 = false ∨ valuationOf q 1376 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause622 (q : Snake 81) (h : Conditions q) : valuation q 1374 = false ∨ valuation q 1376 = true := counterClause622 (baseVal q)

theorem counterClause623 (q : Nat → Bool) : valuationOf q 38 = true ∨ valuationOf q 1379 = true := by
  have hs : count1379 q = (countLit q [-38]) + (countLit q [-40]) := List.countP_append (p := literal q) (l₁ := [-38]) (l₂ := [-40])
  have hm := merge_left (literal (valuationOf q) (-38)) (literal (valuationOf q) (1379)) (countLit q [-38]) (countLit q [-40]) (count1379 q) 1 (meaningNeg38 q) (meaning1379 q) hs
  change (! (valuationOf q 38)) = false ∨ valuationOf q 1379 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause623 (q : Snake 81) (h : Conditions q) : valuation q 38 = true ∨ valuation q 1379 = true := counterClause623 (baseVal q)

theorem counterClause624 (q : Nat → Bool) : valuationOf q 1379 = false ∨ valuationOf q 1381 = true := by
  have hs : count1381 q = (countLit q [-37]) + (countLit q [-38, -40]) := List.countP_append (p := literal q) (l₁ := [-37]) (l₂ := [-38, -40])
  have hm := merge_right (literal (valuationOf q) (1379)) (literal (valuationOf q) (1381)) (countLit q [-37]) (countLit q [-38, -40]) (count1381 q) 1 (meaning1379 q) (meaning1381 q) hs
  change valuationOf q 1379 = false ∨ valuationOf q 1381 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause624 (q : Snake 81) (h : Conditions q) : valuation q 1379 = false ∨ valuation q 1381 = true := counterClause624 (baseVal q)

theorem counterClause625 (q : Nat → Bool) : valuationOf q 37 = true ∨ valuationOf q 1381 = true := by
  have hs : count1381 q = (countLit q [-37]) + (countLit q [-38, -40]) := List.countP_append (p := literal q) (l₁ := [-37]) (l₂ := [-38, -40])
  have hm := merge_left (literal (valuationOf q) (-37)) (literal (valuationOf q) (1381)) (countLit q [-37]) (countLit q [-38, -40]) (count1381 q) 1 (meaningNeg37 q) (meaning1381 q) hs
  change (! (valuationOf q 37)) = false ∨ valuationOf q 1381 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause625 (q : Snake 81) (h : Conditions q) : valuation q 37 = true ∨ valuation q 1381 = true := counterClause625 (baseVal q)

theorem counterClause626 (q : Nat → Bool) : valuationOf q 1381 = false ∨ valuationOf q 1384 = true := by
  have hs : count1384 q = (countLit q [-31, -34, -35]) + (countLit q [-37, -38, -40]) := List.countP_append (p := literal q) (l₁ := [-31, -34, -35]) (l₂ := [-37, -38, -40])
  have hm := merge_right (literal (valuationOf q) (1381)) (literal (valuationOf q) (1384)) (countLit q [-31, -34, -35]) (countLit q [-37, -38, -40]) (count1384 q) 1 (meaning1381 q) (meaning1384 q) hs
  change valuationOf q 1381 = false ∨ valuationOf q 1384 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause626 (q : Snake 81) (h : Conditions q) : valuation q 1381 = false ∨ valuation q 1384 = true := counterClause626 (baseVal q)

theorem counterClause627 (q : Nat → Bool) : valuationOf q 1376 = false ∨ valuationOf q 1384 = true := by
  have hs : count1384 q = (countLit q [-31, -34, -35]) + (countLit q [-37, -38, -40]) := List.countP_append (p := literal q) (l₁ := [-31, -34, -35]) (l₂ := [-37, -38, -40])
  have hm := merge_left (literal (valuationOf q) (1376)) (literal (valuationOf q) (1384)) (countLit q [-31, -34, -35]) (countLit q [-37, -38, -40]) (count1384 q) 1 (meaning1376 q) (meaning1384 q) hs
  change valuationOf q 1376 = false ∨ valuationOf q 1384 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause627 (q : Snake 81) (h : Conditions q) : valuation q 1376 = false ∨ valuation q 1384 = true := counterClause627 (baseVal q)

theorem counterClause628 (q : Nat → Bool) : valuationOf q 1376 = false ∨ valuationOf q 1381 = false ∨ valuationOf q 1385 = true := by
  have hs : count1384 q = (countLit q [-31, -34, -35]) + (countLit q [-37, -38, -40]) := List.countP_append (p := literal q) (l₁ := [-31, -34, -35]) (l₂ := [-37, -38, -40])
  have hm := merge_two (literal (valuationOf q) (1376)) (literal (valuationOf q) (1381)) (literal (valuationOf q) (1385)) (countLit q [-31, -34, -35]) (countLit q [-37, -38, -40]) (count1384 q) 1 1 (meaning1376 q) (meaning1381 q) (meaning1385 q) hs
  change valuationOf q 1376 = false ∨ valuationOf q 1381 = false ∨ valuationOf q 1385 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause628 (q : Snake 81) (h : Conditions q) : valuation q 1376 = false ∨ valuation q 1381 = false ∨ valuation q 1385 = true := counterClause628 (baseVal q)

theorem counterClause629 (q : Nat → Bool) : valuationOf q 46 = true ∨ valuationOf q 1390 = true := by
  have hs : count1390 q = (countLit q [-44]) + (countLit q [-46]) := List.countP_append (p := literal q) (l₁ := [-44]) (l₂ := [-46])
  have hm := merge_right (literal (valuationOf q) (-46)) (literal (valuationOf q) (1390)) (countLit q [-44]) (countLit q [-46]) (count1390 q) 1 (meaningNeg46 q) (meaning1390 q) hs
  change (! (valuationOf q 46)) = false ∨ valuationOf q 1390 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause629 (q : Snake 81) (h : Conditions q) : valuation q 46 = true ∨ valuation q 1390 = true := counterClause629 (baseVal q)

theorem counterClause630 (q : Nat → Bool) : valuationOf q 1390 = false ∨ valuationOf q 1392 = true := by
  have hs : count1392 q = (countLit q [-43]) + (countLit q [-44, -46]) := List.countP_append (p := literal q) (l₁ := [-43]) (l₂ := [-44, -46])
  have hm := merge_right (literal (valuationOf q) (1390)) (literal (valuationOf q) (1392)) (countLit q [-43]) (countLit q [-44, -46]) (count1392 q) 1 (meaning1390 q) (meaning1392 q) hs
  change valuationOf q 1390 = false ∨ valuationOf q 1392 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause630 (q : Snake 81) (h : Conditions q) : valuation q 1390 = false ∨ valuation q 1392 = true := counterClause630 (baseVal q)

theorem counterClause631 (q : Nat → Bool) : valuationOf q 52 = true ∨ valuationOf q 1395 = true := by
  have hs : count1395 q = (countLit q [-49]) + (countLit q [-52]) := List.countP_append (p := literal q) (l₁ := [-49]) (l₂ := [-52])
  have hm := merge_right (literal (valuationOf q) (-52)) (literal (valuationOf q) (1395)) (countLit q [-49]) (countLit q [-52]) (count1395 q) 1 (meaningNeg52 q) (meaning1395 q) hs
  change (! (valuationOf q 52)) = false ∨ valuationOf q 1395 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause631 (q : Snake 81) (h : Conditions q) : valuation q 52 = true ∨ valuation q 1395 = true := counterClause631 (baseVal q)

theorem counterClause632 (q : Nat → Bool) : valuationOf q 49 = true ∨ valuationOf q 1395 = true := by
  have hs : count1395 q = (countLit q [-49]) + (countLit q [-52]) := List.countP_append (p := literal q) (l₁ := [-49]) (l₂ := [-52])
  have hm := merge_left (literal (valuationOf q) (-49)) (literal (valuationOf q) (1395)) (countLit q [-49]) (countLit q [-52]) (count1395 q) 1 (meaningNeg49 q) (meaning1395 q) hs
  change (! (valuationOf q 49)) = false ∨ valuationOf q 1395 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause632 (q : Snake 81) (h : Conditions q) : valuation q 49 = true ∨ valuation q 1395 = true := counterClause632 (baseVal q)

theorem counterClause633 (q : Nat → Bool) : valuationOf q 53 = true ∨ valuationOf q 1397 = true := by
  have hs : count1397 q = (countLit q [-53]) + (countLit q [-54]) := List.countP_append (p := literal q) (l₁ := [-53]) (l₂ := [-54])
  have hm := merge_left (literal (valuationOf q) (-53)) (literal (valuationOf q) (1397)) (countLit q [-53]) (countLit q [-54]) (count1397 q) 1 (meaningNeg53 q) (meaning1397 q) hs
  change (! (valuationOf q 53)) = false ∨ valuationOf q 1397 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause633 (q : Snake 81) (h : Conditions q) : valuation q 53 = true ∨ valuation q 1397 = true := counterClause633 (baseVal q)

theorem counterClause634 (q : Nat → Bool) : valuationOf q 1397 = false ∨ valuationOf q 1399 = true := by
  have hs : count1399 q = (countLit q [-49, -52]) + (countLit q [-53, -54]) := List.countP_append (p := literal q) (l₁ := [-49, -52]) (l₂ := [-53, -54])
  have hm := merge_right (literal (valuationOf q) (1397)) (literal (valuationOf q) (1399)) (countLit q [-49, -52]) (countLit q [-53, -54]) (count1399 q) 1 (meaning1397 q) (meaning1399 q) hs
  change valuationOf q 1397 = false ∨ valuationOf q 1399 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause634 (q : Snake 81) (h : Conditions q) : valuation q 1397 = false ∨ valuation q 1399 = true := counterClause634 (baseVal q)

theorem counterClause635 (q : Nat → Bool) : valuationOf q 1395 = false ∨ valuationOf q 1399 = true := by
  have hs : count1399 q = (countLit q [-49, -52]) + (countLit q [-53, -54]) := List.countP_append (p := literal q) (l₁ := [-49, -52]) (l₂ := [-53, -54])
  have hm := merge_left (literal (valuationOf q) (1395)) (literal (valuationOf q) (1399)) (countLit q [-49, -52]) (countLit q [-53, -54]) (count1399 q) 1 (meaning1395 q) (meaning1399 q) hs
  change valuationOf q 1395 = false ∨ valuationOf q 1399 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause635 (q : Snake 81) (h : Conditions q) : valuation q 1395 = false ∨ valuation q 1399 = true := counterClause635 (baseVal q)

theorem counterClause636 (q : Nat → Bool) : valuationOf q 1395 = false ∨ valuationOf q 1397 = false ∨ valuationOf q 1400 = true := by
  have hs : count1399 q = (countLit q [-49, -52]) + (countLit q [-53, -54]) := List.countP_append (p := literal q) (l₁ := [-49, -52]) (l₂ := [-53, -54])
  have hm := merge_two (literal (valuationOf q) (1395)) (literal (valuationOf q) (1397)) (literal (valuationOf q) (1400)) (countLit q [-49, -52]) (countLit q [-53, -54]) (count1399 q) 1 1 (meaning1395 q) (meaning1397 q) (meaning1400 q) hs
  change valuationOf q 1395 = false ∨ valuationOf q 1397 = false ∨ valuationOf q 1400 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause636 (q : Snake 81) (h : Conditions q) : valuation q 1395 = false ∨ valuation q 1397 = false ∨ valuation q 1400 = true := counterClause636 (baseVal q)

theorem counterClause637 (q : Nat → Bool) : valuationOf q 1399 = false ∨ valuationOf q 1403 = true := by
  have hs : count1403 q = (countLit q [-43, -44, -46]) + (countLit q [-49, -52, -53, -54]) := List.countP_append (p := literal q) (l₁ := [-43, -44, -46]) (l₂ := [-49, -52, -53, -54])
  have hm := merge_right (literal (valuationOf q) (1399)) (literal (valuationOf q) (1403)) (countLit q [-43, -44, -46]) (countLit q [-49, -52, -53, -54]) (count1403 q) 1 (meaning1399 q) (meaning1403 q) hs
  change valuationOf q 1399 = false ∨ valuationOf q 1403 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause637 (q : Snake 81) (h : Conditions q) : valuation q 1399 = false ∨ valuation q 1403 = true := counterClause637 (baseVal q)

theorem counterClause638 (q : Nat → Bool) : valuationOf q 1400 = false ∨ valuationOf q 1404 = true := by
  have hs : count1403 q = (countLit q [-43, -44, -46]) + (countLit q [-49, -52, -53, -54]) := List.countP_append (p := literal q) (l₁ := [-43, -44, -46]) (l₂ := [-49, -52, -53, -54])
  have hm := merge_right (literal (valuationOf q) (1400)) (literal (valuationOf q) (1404)) (countLit q [-43, -44, -46]) (countLit q [-49, -52, -53, -54]) (count1403 q) 2 (meaning1400 q) (meaning1404 q) hs
  change valuationOf q 1400 = false ∨ valuationOf q 1404 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause638 (q : Snake 81) (h : Conditions q) : valuation q 1400 = false ∨ valuation q 1404 = true := counterClause638 (baseVal q)

theorem counterClause639 (q : Nat → Bool) : valuationOf q 1392 = false ∨ valuationOf q 1403 = true := by
  have hs : count1403 q = (countLit q [-43, -44, -46]) + (countLit q [-49, -52, -53, -54]) := List.countP_append (p := literal q) (l₁ := [-43, -44, -46]) (l₂ := [-49, -52, -53, -54])
  have hm := merge_left (literal (valuationOf q) (1392)) (literal (valuationOf q) (1403)) (countLit q [-43, -44, -46]) (countLit q [-49, -52, -53, -54]) (count1403 q) 1 (meaning1392 q) (meaning1403 q) hs
  change valuationOf q 1392 = false ∨ valuationOf q 1403 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause639 (q : Snake 81) (h : Conditions q) : valuation q 1392 = false ∨ valuation q 1403 = true := counterClause639 (baseVal q)

theorem counterClause640 (q : Nat → Bool) : valuationOf q 1404 = false ∨ valuationOf q 1411 = true := by
  have hs : count1410 q = (countLit q [-31, -34, -35, -37, -38, -40]) + (countLit q [-43, -44, -46, -49, -52, -53, -54]) := List.countP_append (p := literal q) (l₁ := [-31, -34, -35, -37, -38, -40]) (l₂ := [-43, -44, -46, -49, -52, -53, -54])
  have hm := merge_right (literal (valuationOf q) (1404)) (literal (valuationOf q) (1411)) (countLit q [-31, -34, -35, -37, -38, -40]) (countLit q [-43, -44, -46, -49, -52, -53, -54]) (count1410 q) 2 (meaning1404 q) (meaning1411 q) hs
  change valuationOf q 1404 = false ∨ valuationOf q 1411 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause640 (q : Snake 81) (h : Conditions q) : valuation q 1404 = false ∨ valuation q 1411 = true := counterClause640 (baseVal q)

theorem block19 (q : Snake 81) (h : Conditions q) : B112E123.Block19 (valuation q) :=
  ⟨clause609 q h, clause610 q h, clause611 q h, clause612 q h, clause613 q h, clause614 q h, clause615 q h, clause616 q h, clause617 q h, clause618 q h, clause619 q h, clause620 q h, clause621 q h, clause622 q h, clause623 q h, clause624 q h, clause625 q h, clause626 q h, clause627 q h, clause628 q h, clause629 q h, clause630 q h, clause631 q h, clause632 q h, clause633 q h, clause634 q h, clause635 q h, clause636 q h, clause637 q h, clause638 q h, clause639 q h, clause640 q h⟩

end
end Snake9.Regrowth.E112123
