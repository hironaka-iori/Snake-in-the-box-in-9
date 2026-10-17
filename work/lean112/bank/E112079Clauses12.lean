import E112079Semantics
import B112E079Inputs
namespace Snake9.Regrowth.E112079
noncomputable section
local instance blockDec12 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause385 (q : Nat → Bool) : valuationOf q 1343 = false ∨ valuationOf q 1362 = false ∨ valuationOf q 1370 = true := by
  have hs : count1369 q = (countLit q [-2, -4, -5, -7, -10, -11]) + (countLit q [-12, -16, -17, -21, -22, -24, -27]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5, -7, -10, -11]) (l₂ := [-12, -16, -17, -21, -22, -24, -27])
  have hm := merge_two (literal (valuationOf q) (1343)) (literal (valuationOf q) (1362)) (literal (valuationOf q) (1370)) (countLit q [-2, -4, -5, -7, -10, -11]) (countLit q [-12, -16, -17, -21, -22, -24, -27]) (count1369 q) 1 1 (meaning1343 q) (meaning1362 q) (meaning1370 q) hs
  change valuationOf q 1343 = false ∨ valuationOf q 1362 = false ∨ valuationOf q 1370 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause385 (q : Snake 81) (h : Conditions q) : valuation q 1343 = false ∨ valuation q 1362 = false ∨ valuation q 1370 = true := counterClause385 (baseVal q)

theorem counterClause386 (q : Nat → Bool) : valuationOf q 1343 = false ∨ valuationOf q 1363 = false ∨ valuationOf q 1371 = true := by
  have hs : count1369 q = (countLit q [-2, -4, -5, -7, -10, -11]) + (countLit q [-12, -16, -17, -21, -22, -24, -27]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5, -7, -10, -11]) (l₂ := [-12, -16, -17, -21, -22, -24, -27])
  have hm := merge_two (literal (valuationOf q) (1343)) (literal (valuationOf q) (1363)) (literal (valuationOf q) (1371)) (countLit q [-2, -4, -5, -7, -10, -11]) (countLit q [-12, -16, -17, -21, -22, -24, -27]) (count1369 q) 1 2 (meaning1343 q) (meaning1363 q) (meaning1371 q) hs
  change valuationOf q 1343 = false ∨ valuationOf q 1363 = false ∨ valuationOf q 1371 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause386 (q : Snake 81) (h : Conditions q) : valuation q 1343 = false ∨ valuation q 1363 = false ∨ valuation q 1371 = true := counterClause386 (baseVal q)

theorem counterClause387 (q : Nat → Bool) : valuationOf q 1343 = false ∨ valuationOf q 1364 = false ∨ valuationOf q 1372 = true := by
  have hs : count1369 q = (countLit q [-2, -4, -5, -7, -10, -11]) + (countLit q [-12, -16, -17, -21, -22, -24, -27]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5, -7, -10, -11]) (l₂ := [-12, -16, -17, -21, -22, -24, -27])
  have hm := merge_two (literal (valuationOf q) (1343)) (literal (valuationOf q) (1364)) (literal (valuationOf q) (1372)) (countLit q [-2, -4, -5, -7, -10, -11]) (countLit q [-12, -16, -17, -21, -22, -24, -27]) (count1369 q) 1 3 (meaning1343 q) (meaning1364 q) (meaning1372 q) hs
  change valuationOf q 1343 = false ∨ valuationOf q 1364 = false ∨ valuationOf q 1372 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause387 (q : Snake 81) (h : Conditions q) : valuation q 1343 = false ∨ valuation q 1364 = false ∨ valuation q 1372 = true := counterClause387 (baseVal q)

theorem counterClause388 (q : Nat → Bool) : valuationOf q 1344 = false ∨ valuationOf q 1362 = false ∨ valuationOf q 1371 = true := by
  have hs : count1369 q = (countLit q [-2, -4, -5, -7, -10, -11]) + (countLit q [-12, -16, -17, -21, -22, -24, -27]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5, -7, -10, -11]) (l₂ := [-12, -16, -17, -21, -22, -24, -27])
  have hm := merge_two (literal (valuationOf q) (1344)) (literal (valuationOf q) (1362)) (literal (valuationOf q) (1371)) (countLit q [-2, -4, -5, -7, -10, -11]) (countLit q [-12, -16, -17, -21, -22, -24, -27]) (count1369 q) 2 1 (meaning1344 q) (meaning1362 q) (meaning1371 q) hs
  change valuationOf q 1344 = false ∨ valuationOf q 1362 = false ∨ valuationOf q 1371 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause388 (q : Snake 81) (h : Conditions q) : valuation q 1344 = false ∨ valuation q 1362 = false ∨ valuation q 1371 = true := counterClause388 (baseVal q)

theorem counterClause389 (q : Nat → Bool) : valuationOf q 1344 = false ∨ valuationOf q 1363 = false ∨ valuationOf q 1372 = true := by
  have hs : count1369 q = (countLit q [-2, -4, -5, -7, -10, -11]) + (countLit q [-12, -16, -17, -21, -22, -24, -27]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5, -7, -10, -11]) (l₂ := [-12, -16, -17, -21, -22, -24, -27])
  have hm := merge_two (literal (valuationOf q) (1344)) (literal (valuationOf q) (1363)) (literal (valuationOf q) (1372)) (countLit q [-2, -4, -5, -7, -10, -11]) (countLit q [-12, -16, -17, -21, -22, -24, -27]) (count1369 q) 2 2 (meaning1344 q) (meaning1363 q) (meaning1372 q) hs
  change valuationOf q 1344 = false ∨ valuationOf q 1363 = false ∨ valuationOf q 1372 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause389 (q : Snake 81) (h : Conditions q) : valuation q 1344 = false ∨ valuation q 1363 = false ∨ valuation q 1372 = true := counterClause389 (baseVal q)

theorem counterClause390 (q : Nat → Bool) : valuationOf q 1344 = false ∨ valuationOf q 1364 = false ∨ valuationOf q 1373 = true := by
  have hs : count1369 q = (countLit q [-2, -4, -5, -7, -10, -11]) + (countLit q [-12, -16, -17, -21, -22, -24, -27]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5, -7, -10, -11]) (l₂ := [-12, -16, -17, -21, -22, -24, -27])
  have hm := merge_two (literal (valuationOf q) (1344)) (literal (valuationOf q) (1364)) (literal (valuationOf q) (1373)) (countLit q [-2, -4, -5, -7, -10, -11]) (countLit q [-12, -16, -17, -21, -22, -24, -27]) (count1369 q) 2 3 (meaning1344 q) (meaning1364 q) (meaning1373 q) hs
  change valuationOf q 1344 = false ∨ valuationOf q 1364 = false ∨ valuationOf q 1373 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause390 (q : Snake 81) (h : Conditions q) : valuation q 1344 = false ∨ valuation q 1364 = false ∨ valuation q 1373 = true := counterClause390 (baseVal q)

theorem counterClause391 (q : Nat → Bool) : valuationOf q 33 = true ∨ valuationOf q 1381 = true := by
  have hs : count1381 q = (countLit q [-30]) + (countLit q [-33]) := List.countP_append (p := literal q) (l₁ := [-30]) (l₂ := [-33])
  have hm := merge_right (literal (valuationOf q) (-33)) (literal (valuationOf q) (1381)) (countLit q [-30]) (countLit q [-33]) (count1381 q) 1 (meaningNeg33 q) (meaning1381 q) hs
  change (! (valuationOf q 33)) = false ∨ valuationOf q 1381 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause391 (q : Snake 81) (h : Conditions q) : valuation q 33 = true ∨ valuation q 1381 = true := counterClause391 (baseVal q)

theorem counterClause392 (q : Nat → Bool) : valuationOf q 30 = true ∨ valuationOf q 1381 = true := by
  have hs : count1381 q = (countLit q [-30]) + (countLit q [-33]) := List.countP_append (p := literal q) (l₁ := [-30]) (l₂ := [-33])
  have hm := merge_left (literal (valuationOf q) (-30)) (literal (valuationOf q) (1381)) (countLit q [-30]) (countLit q [-33]) (count1381 q) 1 (meaningNeg30 q) (meaning1381 q) hs
  change (! (valuationOf q 30)) = false ∨ valuationOf q 1381 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause392 (q : Snake 81) (h : Conditions q) : valuation q 30 = true ∨ valuation q 1381 = true := counterClause392 (baseVal q)

theorem counterClause393 (q : Nat → Bool) : valuationOf q 30 = true ∨ valuationOf q 33 = true ∨ valuationOf q 1382 = true := by
  have hs : count1381 q = (countLit q [-30]) + (countLit q [-33]) := List.countP_append (p := literal q) (l₁ := [-30]) (l₂ := [-33])
  have hm := merge_two (literal (valuationOf q) (-30)) (literal (valuationOf q) (-33)) (literal (valuationOf q) (1382)) (countLit q [-30]) (countLit q [-33]) (count1381 q) 1 1 (meaningNeg30 q) (meaningNeg33 q) (meaning1382 q) hs
  change (! (valuationOf q 30)) = false ∨ (! (valuationOf q 33)) = false ∨ valuationOf q 1382 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause393 (q : Snake 81) (h : Conditions q) : valuation q 30 = true ∨ valuation q 33 = true ∨ valuation q 1382 = true := counterClause393 (baseVal q)

theorem counterClause394 (q : Nat → Bool) : valuationOf q 1381 = false ∨ valuationOf q 1383 = true := by
  have hs : count1383 q = (countLit q [-28]) + (countLit q [-30, -33]) := List.countP_append (p := literal q) (l₁ := [-28]) (l₂ := [-30, -33])
  have hm := merge_right (literal (valuationOf q) (1381)) (literal (valuationOf q) (1383)) (countLit q [-28]) (countLit q [-30, -33]) (count1383 q) 1 (meaning1381 q) (meaning1383 q) hs
  change valuationOf q 1381 = false ∨ valuationOf q 1383 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause394 (q : Snake 81) (h : Conditions q) : valuation q 1381 = false ∨ valuation q 1383 = true := counterClause394 (baseVal q)

theorem counterClause395 (q : Nat → Bool) : valuationOf q 1382 = false ∨ valuationOf q 1384 = true := by
  have hs : count1383 q = (countLit q [-28]) + (countLit q [-30, -33]) := List.countP_append (p := literal q) (l₁ := [-28]) (l₂ := [-30, -33])
  have hm := merge_right (literal (valuationOf q) (1382)) (literal (valuationOf q) (1384)) (countLit q [-28]) (countLit q [-30, -33]) (count1383 q) 2 (meaning1382 q) (meaning1384 q) hs
  change valuationOf q 1382 = false ∨ valuationOf q 1384 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause395 (q : Snake 81) (h : Conditions q) : valuation q 1382 = false ∨ valuation q 1384 = true := counterClause395 (baseVal q)

theorem counterClause396 (q : Nat → Bool) : valuationOf q 28 = true ∨ valuationOf q 1383 = true := by
  have hs : count1383 q = (countLit q [-28]) + (countLit q [-30, -33]) := List.countP_append (p := literal q) (l₁ := [-28]) (l₂ := [-30, -33])
  have hm := merge_left (literal (valuationOf q) (-28)) (literal (valuationOf q) (1383)) (countLit q [-28]) (countLit q [-30, -33]) (count1383 q) 1 (meaningNeg28 q) (meaning1383 q) hs
  change (! (valuationOf q 28)) = false ∨ valuationOf q 1383 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause396 (q : Snake 81) (h : Conditions q) : valuation q 28 = true ∨ valuation q 1383 = true := counterClause396 (baseVal q)

theorem counterClause397 (q : Nat → Bool) : valuationOf q 28 = true ∨ valuationOf q 1381 = false ∨ valuationOf q 1384 = true := by
  have hs : count1383 q = (countLit q [-28]) + (countLit q [-30, -33]) := List.countP_append (p := literal q) (l₁ := [-28]) (l₂ := [-30, -33])
  have hm := merge_two (literal (valuationOf q) (-28)) (literal (valuationOf q) (1381)) (literal (valuationOf q) (1384)) (countLit q [-28]) (countLit q [-30, -33]) (count1383 q) 1 1 (meaningNeg28 q) (meaning1381 q) (meaning1384 q) hs
  change (! (valuationOf q 28)) = false ∨ valuationOf q 1381 = false ∨ valuationOf q 1384 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause397 (q : Snake 81) (h : Conditions q) : valuation q 28 = true ∨ valuation q 1381 = false ∨ valuation q 1384 = true := counterClause397 (baseVal q)

theorem counterClause398 (q : Nat → Bool) : valuationOf q 28 = true ∨ valuationOf q 1382 = false ∨ valuationOf q 1385 = true := by
  have hs : count1383 q = (countLit q [-28]) + (countLit q [-30, -33]) := List.countP_append (p := literal q) (l₁ := [-28]) (l₂ := [-30, -33])
  have hm := merge_two (literal (valuationOf q) (-28)) (literal (valuationOf q) (1382)) (literal (valuationOf q) (1385)) (countLit q [-28]) (countLit q [-30, -33]) (count1383 q) 1 2 (meaningNeg28 q) (meaning1382 q) (meaning1385 q) hs
  change (! (valuationOf q 28)) = false ∨ valuationOf q 1382 = false ∨ valuationOf q 1385 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause398 (q : Snake 81) (h : Conditions q) : valuation q 28 = true ∨ valuation q 1382 = false ∨ valuation q 1385 = true := counterClause398 (baseVal q)

theorem counterClause399 (q : Nat → Bool) : valuationOf q 40 = true ∨ valuationOf q 1386 = true := by
  have hs : count1386 q = (countLit q [-37]) + (countLit q [-40]) := List.countP_append (p := literal q) (l₁ := [-37]) (l₂ := [-40])
  have hm := merge_right (literal (valuationOf q) (-40)) (literal (valuationOf q) (1386)) (countLit q [-37]) (countLit q [-40]) (count1386 q) 1 (meaningNeg40 q) (meaning1386 q) hs
  change (! (valuationOf q 40)) = false ∨ valuationOf q 1386 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause399 (q : Snake 81) (h : Conditions q) : valuation q 40 = true ∨ valuation q 1386 = true := counterClause399 (baseVal q)

theorem counterClause400 (q : Nat → Bool) : valuationOf q 37 = true ∨ valuationOf q 1386 = true := by
  have hs : count1386 q = (countLit q [-37]) + (countLit q [-40]) := List.countP_append (p := literal q) (l₁ := [-37]) (l₂ := [-40])
  have hm := merge_left (literal (valuationOf q) (-37)) (literal (valuationOf q) (1386)) (countLit q [-37]) (countLit q [-40]) (count1386 q) 1 (meaningNeg37 q) (meaning1386 q) hs
  change (! (valuationOf q 37)) = false ∨ valuationOf q 1386 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause400 (q : Snake 81) (h : Conditions q) : valuation q 37 = true ∨ valuation q 1386 = true := counterClause400 (baseVal q)

theorem counterClause401 (q : Nat → Bool) : valuationOf q 37 = true ∨ valuationOf q 40 = true ∨ valuationOf q 1387 = true := by
  have hs : count1386 q = (countLit q [-37]) + (countLit q [-40]) := List.countP_append (p := literal q) (l₁ := [-37]) (l₂ := [-40])
  have hm := merge_two (literal (valuationOf q) (-37)) (literal (valuationOf q) (-40)) (literal (valuationOf q) (1387)) (countLit q [-37]) (countLit q [-40]) (count1386 q) 1 1 (meaningNeg37 q) (meaningNeg40 q) (meaning1387 q) hs
  change (! (valuationOf q 37)) = false ∨ (! (valuationOf q 40)) = false ∨ valuationOf q 1387 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause401 (q : Snake 81) (h : Conditions q) : valuation q 37 = true ∨ valuation q 40 = true ∨ valuation q 1387 = true := counterClause401 (baseVal q)

theorem counterClause402 (q : Nat → Bool) : valuationOf q 1386 = false ∨ valuationOf q 1388 = true := by
  have hs : count1388 q = (countLit q [-36]) + (countLit q [-37, -40]) := List.countP_append (p := literal q) (l₁ := [-36]) (l₂ := [-37, -40])
  have hm := merge_right (literal (valuationOf q) (1386)) (literal (valuationOf q) (1388)) (countLit q [-36]) (countLit q [-37, -40]) (count1388 q) 1 (meaning1386 q) (meaning1388 q) hs
  change valuationOf q 1386 = false ∨ valuationOf q 1388 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause402 (q : Snake 81) (h : Conditions q) : valuation q 1386 = false ∨ valuation q 1388 = true := counterClause402 (baseVal q)

theorem counterClause403 (q : Nat → Bool) : valuationOf q 1387 = false ∨ valuationOf q 1389 = true := by
  have hs : count1388 q = (countLit q [-36]) + (countLit q [-37, -40]) := List.countP_append (p := literal q) (l₁ := [-36]) (l₂ := [-37, -40])
  have hm := merge_right (literal (valuationOf q) (1387)) (literal (valuationOf q) (1389)) (countLit q [-36]) (countLit q [-37, -40]) (count1388 q) 2 (meaning1387 q) (meaning1389 q) hs
  change valuationOf q 1387 = false ∨ valuationOf q 1389 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause403 (q : Snake 81) (h : Conditions q) : valuation q 1387 = false ∨ valuation q 1389 = true := counterClause403 (baseVal q)

theorem counterClause404 (q : Nat → Bool) : valuationOf q 36 = true ∨ valuationOf q 1388 = true := by
  have hs : count1388 q = (countLit q [-36]) + (countLit q [-37, -40]) := List.countP_append (p := literal q) (l₁ := [-36]) (l₂ := [-37, -40])
  have hm := merge_left (literal (valuationOf q) (-36)) (literal (valuationOf q) (1388)) (countLit q [-36]) (countLit q [-37, -40]) (count1388 q) 1 (meaningNeg36 q) (meaning1388 q) hs
  change (! (valuationOf q 36)) = false ∨ valuationOf q 1388 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause404 (q : Snake 81) (h : Conditions q) : valuation q 36 = true ∨ valuation q 1388 = true := counterClause404 (baseVal q)

theorem counterClause405 (q : Nat → Bool) : valuationOf q 36 = true ∨ valuationOf q 1386 = false ∨ valuationOf q 1389 = true := by
  have hs : count1388 q = (countLit q [-36]) + (countLit q [-37, -40]) := List.countP_append (p := literal q) (l₁ := [-36]) (l₂ := [-37, -40])
  have hm := merge_two (literal (valuationOf q) (-36)) (literal (valuationOf q) (1386)) (literal (valuationOf q) (1389)) (countLit q [-36]) (countLit q [-37, -40]) (count1388 q) 1 1 (meaningNeg36 q) (meaning1386 q) (meaning1389 q) hs
  change (! (valuationOf q 36)) = false ∨ valuationOf q 1386 = false ∨ valuationOf q 1389 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause405 (q : Snake 81) (h : Conditions q) : valuation q 36 = true ∨ valuation q 1386 = false ∨ valuation q 1389 = true := counterClause405 (baseVal q)

theorem counterClause406 (q : Nat → Bool) : valuationOf q 1388 = false ∨ valuationOf q 1391 = true := by
  have hs : count1391 q = (countLit q [-28, -30, -33]) + (countLit q [-36, -37, -40]) := List.countP_append (p := literal q) (l₁ := [-28, -30, -33]) (l₂ := [-36, -37, -40])
  have hm := merge_right (literal (valuationOf q) (1388)) (literal (valuationOf q) (1391)) (countLit q [-28, -30, -33]) (countLit q [-36, -37, -40]) (count1391 q) 1 (meaning1388 q) (meaning1391 q) hs
  change valuationOf q 1388 = false ∨ valuationOf q 1391 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause406 (q : Snake 81) (h : Conditions q) : valuation q 1388 = false ∨ valuation q 1391 = true := counterClause406 (baseVal q)

theorem counterClause407 (q : Nat → Bool) : valuationOf q 1383 = false ∨ valuationOf q 1391 = true := by
  have hs : count1391 q = (countLit q [-28, -30, -33]) + (countLit q [-36, -37, -40]) := List.countP_append (p := literal q) (l₁ := [-28, -30, -33]) (l₂ := [-36, -37, -40])
  have hm := merge_left (literal (valuationOf q) (1383)) (literal (valuationOf q) (1391)) (countLit q [-28, -30, -33]) (countLit q [-36, -37, -40]) (count1391 q) 1 (meaning1383 q) (meaning1391 q) hs
  change valuationOf q 1383 = false ∨ valuationOf q 1391 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause407 (q : Snake 81) (h : Conditions q) : valuation q 1383 = false ∨ valuation q 1391 = true := counterClause407 (baseVal q)

theorem counterClause408 (q : Nat → Bool) : valuationOf q 1383 = false ∨ valuationOf q 1388 = false ∨ valuationOf q 1392 = true := by
  have hs : count1391 q = (countLit q [-28, -30, -33]) + (countLit q [-36, -37, -40]) := List.countP_append (p := literal q) (l₁ := [-28, -30, -33]) (l₂ := [-36, -37, -40])
  have hm := merge_two (literal (valuationOf q) (1383)) (literal (valuationOf q) (1388)) (literal (valuationOf q) (1392)) (countLit q [-28, -30, -33]) (countLit q [-36, -37, -40]) (count1391 q) 1 1 (meaning1383 q) (meaning1388 q) (meaning1392 q) hs
  change valuationOf q 1383 = false ∨ valuationOf q 1388 = false ∨ valuationOf q 1392 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause408 (q : Snake 81) (h : Conditions q) : valuation q 1383 = false ∨ valuation q 1388 = false ∨ valuation q 1392 = true := counterClause408 (baseVal q)

theorem counterClause409 (q : Nat → Bool) : valuationOf q 1383 = false ∨ valuationOf q 1389 = false ∨ valuationOf q 1393 = true := by
  have hs : count1391 q = (countLit q [-28, -30, -33]) + (countLit q [-36, -37, -40]) := List.countP_append (p := literal q) (l₁ := [-28, -30, -33]) (l₂ := [-36, -37, -40])
  have hm := merge_two (literal (valuationOf q) (1383)) (literal (valuationOf q) (1389)) (literal (valuationOf q) (1393)) (countLit q [-28, -30, -33]) (countLit q [-36, -37, -40]) (count1391 q) 1 2 (meaning1383 q) (meaning1389 q) (meaning1393 q) hs
  change valuationOf q 1383 = false ∨ valuationOf q 1389 = false ∨ valuationOf q 1393 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause409 (q : Snake 81) (h : Conditions q) : valuation q 1383 = false ∨ valuation q 1389 = false ∨ valuation q 1393 = true := counterClause409 (baseVal q)

theorem counterClause410 (q : Nat → Bool) : valuationOf q 1384 = false ∨ valuationOf q 1392 = true := by
  have hs : count1391 q = (countLit q [-28, -30, -33]) + (countLit q [-36, -37, -40]) := List.countP_append (p := literal q) (l₁ := [-28, -30, -33]) (l₂ := [-36, -37, -40])
  have hm := merge_left (literal (valuationOf q) (1384)) (literal (valuationOf q) (1392)) (countLit q [-28, -30, -33]) (countLit q [-36, -37, -40]) (count1391 q) 2 (meaning1384 q) (meaning1392 q) hs
  change valuationOf q 1384 = false ∨ valuationOf q 1392 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause410 (q : Snake 81) (h : Conditions q) : valuation q 1384 = false ∨ valuation q 1392 = true := counterClause410 (baseVal q)

theorem counterClause411 (q : Nat → Bool) : valuationOf q 1384 = false ∨ valuationOf q 1388 = false ∨ valuationOf q 1393 = true := by
  have hs : count1391 q = (countLit q [-28, -30, -33]) + (countLit q [-36, -37, -40]) := List.countP_append (p := literal q) (l₁ := [-28, -30, -33]) (l₂ := [-36, -37, -40])
  have hm := merge_two (literal (valuationOf q) (1384)) (literal (valuationOf q) (1388)) (literal (valuationOf q) (1393)) (countLit q [-28, -30, -33]) (countLit q [-36, -37, -40]) (count1391 q) 2 1 (meaning1384 q) (meaning1388 q) (meaning1393 q) hs
  change valuationOf q 1384 = false ∨ valuationOf q 1388 = false ∨ valuationOf q 1393 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause411 (q : Snake 81) (h : Conditions q) : valuation q 1384 = false ∨ valuation q 1388 = false ∨ valuation q 1393 = true := counterClause411 (baseVal q)

theorem counterClause412 (q : Nat → Bool) : valuationOf q 1385 = false ∨ valuationOf q 1388 = false ∨ valuationOf q 1394 = true := by
  have hs : count1391 q = (countLit q [-28, -30, -33]) + (countLit q [-36, -37, -40]) := List.countP_append (p := literal q) (l₁ := [-28, -30, -33]) (l₂ := [-36, -37, -40])
  have hm := merge_two (literal (valuationOf q) (1385)) (literal (valuationOf q) (1388)) (literal (valuationOf q) (1394)) (countLit q [-28, -30, -33]) (countLit q [-36, -37, -40]) (count1391 q) 3 1 (meaning1385 q) (meaning1388 q) (meaning1394 q) hs
  change valuationOf q 1385 = false ∨ valuationOf q 1388 = false ∨ valuationOf q 1394 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause412 (q : Snake 81) (h : Conditions q) : valuation q 1385 = false ∨ valuation q 1388 = false ∨ valuation q 1394 = true := counterClause412 (baseVal q)

theorem counterClause413 (q : Nat → Bool) : valuationOf q 47 = true ∨ valuationOf q 1397 = true := by
  have hs : count1397 q = (countLit q [-45]) + (countLit q [-47]) := List.countP_append (p := literal q) (l₁ := [-45]) (l₂ := [-47])
  have hm := merge_right (literal (valuationOf q) (-47)) (literal (valuationOf q) (1397)) (countLit q [-45]) (countLit q [-47]) (count1397 q) 1 (meaningNeg47 q) (meaning1397 q) hs
  change (! (valuationOf q 47)) = false ∨ valuationOf q 1397 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause413 (q : Snake 81) (h : Conditions q) : valuation q 47 = true ∨ valuation q 1397 = true := counterClause413 (baseVal q)

theorem counterClause414 (q : Nat → Bool) : valuationOf q 45 = true ∨ valuationOf q 1397 = true := by
  have hs : count1397 q = (countLit q [-45]) + (countLit q [-47]) := List.countP_append (p := literal q) (l₁ := [-45]) (l₂ := [-47])
  have hm := merge_left (literal (valuationOf q) (-45)) (literal (valuationOf q) (1397)) (countLit q [-45]) (countLit q [-47]) (count1397 q) 1 (meaningNeg45 q) (meaning1397 q) hs
  change (! (valuationOf q 45)) = false ∨ valuationOf q 1397 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause414 (q : Snake 81) (h : Conditions q) : valuation q 45 = true ∨ valuation q 1397 = true := counterClause414 (baseVal q)

theorem counterClause415 (q : Nat → Bool) : valuationOf q 1397 = false ∨ valuationOf q 1399 = true := by
  have hs : count1399 q = (countLit q [-42]) + (countLit q [-45, -47]) := List.countP_append (p := literal q) (l₁ := [-42]) (l₂ := [-45, -47])
  have hm := merge_right (literal (valuationOf q) (1397)) (literal (valuationOf q) (1399)) (countLit q [-42]) (countLit q [-45, -47]) (count1399 q) 1 (meaning1397 q) (meaning1399 q) hs
  change valuationOf q 1397 = false ∨ valuationOf q 1399 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause415 (q : Snake 81) (h : Conditions q) : valuation q 1397 = false ∨ valuation q 1399 = true := counterClause415 (baseVal q)

theorem counterClause416 (q : Nat → Bool) : valuationOf q 42 = true ∨ valuationOf q 1399 = true := by
  have hs : count1399 q = (countLit q [-42]) + (countLit q [-45, -47]) := List.countP_append (p := literal q) (l₁ := [-42]) (l₂ := [-45, -47])
  have hm := merge_left (literal (valuationOf q) (-42)) (literal (valuationOf q) (1399)) (countLit q [-42]) (countLit q [-45, -47]) (count1399 q) 1 (meaningNeg42 q) (meaning1399 q) hs
  change (! (valuationOf q 42)) = false ∨ valuationOf q 1399 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause416 (q : Snake 81) (h : Conditions q) : valuation q 42 = true ∨ valuation q 1399 = true := counterClause416 (baseVal q)

theorem block12 (q : Snake 81) (h : Conditions q) : B112E079.Block12 (valuation q) :=
  ⟨clause385 q h, clause386 q h, clause387 q h, clause388 q h, clause389 q h, clause390 q h, clause391 q h, clause392 q h, clause393 q h, clause394 q h, clause395 q h, clause396 q h, clause397 q h, clause398 q h, clause399 q h, clause400 q h, clause401 q h, clause402 q h, clause403 q h, clause404 q h, clause405 q h, clause406 q h, clause407 q h, clause408 q h, clause409 q h, clause410 q h, clause411 q h, clause412 q h, clause413 q h, clause414 q h, clause415 q h, clause416 q h⟩

end
end Snake9.Regrowth.E112079
