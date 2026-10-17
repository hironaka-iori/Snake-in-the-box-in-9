import E112058Semantics
import B112E058Inputs
namespace Snake9.Regrowth.E112058
noncomputable section
local instance blockDec12 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause385 (q : Nat → Bool) : valuationOf q 1415 = false ∨ valuationOf q 1434 = false ∨ valuationOf q 1443 = true := by
  have hs : count1441 q = (countLit q [-2, -5, -6, -10, -11, -13, -15]) + (countLit q [-18, -20, -22, -23, -24, -27, -30]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -6, -10, -11, -13, -15]) (l₂ := [-18, -20, -22, -23, -24, -27, -30])
  have hm := merge_two (literal (valuationOf q) (1415)) (literal (valuationOf q) (1434)) (literal (valuationOf q) (1443)) (countLit q [-2, -5, -6, -10, -11, -13, -15]) (countLit q [-18, -20, -22, -23, -24, -27, -30]) (count1441 q) 2 1 (meaning1415 q) (meaning1434 q) (meaning1443 q) hs
  change valuationOf q 1415 = false ∨ valuationOf q 1434 = false ∨ valuationOf q 1443 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause385 (q : Snake 81) (h : Conditions q) : valuation q 1415 = false ∨ valuation q 1434 = false ∨ valuation q 1443 = true := counterClause385 (baseVal q)

theorem counterClause386 (q : Nat → Bool) : valuationOf q 1415 = false ∨ valuationOf q 1435 = false ∨ valuationOf q 1444 = true := by
  have hs : count1441 q = (countLit q [-2, -5, -6, -10, -11, -13, -15]) + (countLit q [-18, -20, -22, -23, -24, -27, -30]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -6, -10, -11, -13, -15]) (l₂ := [-18, -20, -22, -23, -24, -27, -30])
  have hm := merge_two (literal (valuationOf q) (1415)) (literal (valuationOf q) (1435)) (literal (valuationOf q) (1444)) (countLit q [-2, -5, -6, -10, -11, -13, -15]) (countLit q [-18, -20, -22, -23, -24, -27, -30]) (count1441 q) 2 2 (meaning1415 q) (meaning1435 q) (meaning1444 q) hs
  change valuationOf q 1415 = false ∨ valuationOf q 1435 = false ∨ valuationOf q 1444 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause386 (q : Snake 81) (h : Conditions q) : valuation q 1415 = false ∨ valuation q 1435 = false ∨ valuation q 1444 = true := counterClause386 (baseVal q)

theorem counterClause387 (q : Nat → Bool) : valuationOf q 1415 = false ∨ valuationOf q 1436 = false ∨ valuationOf q 1445 = true := by
  have hs : count1441 q = (countLit q [-2, -5, -6, -10, -11, -13, -15]) + (countLit q [-18, -20, -22, -23, -24, -27, -30]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -6, -10, -11, -13, -15]) (l₂ := [-18, -20, -22, -23, -24, -27, -30])
  have hm := merge_two (literal (valuationOf q) (1415)) (literal (valuationOf q) (1436)) (literal (valuationOf q) (1445)) (countLit q [-2, -5, -6, -10, -11, -13, -15]) (countLit q [-18, -20, -22, -23, -24, -27, -30]) (count1441 q) 2 3 (meaning1415 q) (meaning1436 q) (meaning1445 q) hs
  change valuationOf q 1415 = false ∨ valuationOf q 1436 = false ∨ valuationOf q 1445 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause387 (q : Snake 81) (h : Conditions q) : valuation q 1415 = false ∨ valuation q 1436 = false ∨ valuation q 1445 = true := counterClause387 (baseVal q)

theorem counterClause388 (q : Nat → Bool) : valuationOf q 1415 = false ∨ valuationOf q 1437 = false ∨ valuationOf q 1446 = true := by
  have hs : count1441 q = (countLit q [-2, -5, -6, -10, -11, -13, -15]) + (countLit q [-18, -20, -22, -23, -24, -27, -30]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -6, -10, -11, -13, -15]) (l₂ := [-18, -20, -22, -23, -24, -27, -30])
  have hm := merge_two (literal (valuationOf q) (1415)) (literal (valuationOf q) (1437)) (literal (valuationOf q) (1446)) (countLit q [-2, -5, -6, -10, -11, -13, -15]) (countLit q [-18, -20, -22, -23, -24, -27, -30]) (count1441 q) 2 4 (meaning1415 q) (meaning1437 q) (meaning1446 q) hs
  change valuationOf q 1415 = false ∨ valuationOf q 1437 = false ∨ valuationOf q 1446 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause388 (q : Snake 81) (h : Conditions q) : valuation q 1415 = false ∨ valuation q 1437 = false ∨ valuation q 1446 = true := counterClause388 (baseVal q)

theorem counterClause389 (q : Nat → Bool) : valuationOf q 1416 = false ∨ valuationOf q 1434 = false ∨ valuationOf q 1444 = true := by
  have hs : count1441 q = (countLit q [-2, -5, -6, -10, -11, -13, -15]) + (countLit q [-18, -20, -22, -23, -24, -27, -30]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -6, -10, -11, -13, -15]) (l₂ := [-18, -20, -22, -23, -24, -27, -30])
  have hm := merge_two (literal (valuationOf q) (1416)) (literal (valuationOf q) (1434)) (literal (valuationOf q) (1444)) (countLit q [-2, -5, -6, -10, -11, -13, -15]) (countLit q [-18, -20, -22, -23, -24, -27, -30]) (count1441 q) 3 1 (meaning1416 q) (meaning1434 q) (meaning1444 q) hs
  change valuationOf q 1416 = false ∨ valuationOf q 1434 = false ∨ valuationOf q 1444 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause389 (q : Snake 81) (h : Conditions q) : valuation q 1416 = false ∨ valuation q 1434 = false ∨ valuation q 1444 = true := counterClause389 (baseVal q)

theorem counterClause390 (q : Nat → Bool) : valuationOf q 1416 = false ∨ valuationOf q 1435 = false ∨ valuationOf q 1445 = true := by
  have hs : count1441 q = (countLit q [-2, -5, -6, -10, -11, -13, -15]) + (countLit q [-18, -20, -22, -23, -24, -27, -30]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -6, -10, -11, -13, -15]) (l₂ := [-18, -20, -22, -23, -24, -27, -30])
  have hm := merge_two (literal (valuationOf q) (1416)) (literal (valuationOf q) (1435)) (literal (valuationOf q) (1445)) (countLit q [-2, -5, -6, -10, -11, -13, -15]) (countLit q [-18, -20, -22, -23, -24, -27, -30]) (count1441 q) 3 2 (meaning1416 q) (meaning1435 q) (meaning1445 q) hs
  change valuationOf q 1416 = false ∨ valuationOf q 1435 = false ∨ valuationOf q 1445 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause390 (q : Snake 81) (h : Conditions q) : valuation q 1416 = false ∨ valuation q 1435 = false ∨ valuation q 1445 = true := counterClause390 (baseVal q)

theorem counterClause391 (q : Nat → Bool) : valuationOf q 1416 = false ∨ valuationOf q 1437 = false ∨ valuationOf q 1447 = true := by
  have hs : count1441 q = (countLit q [-2, -5, -6, -10, -11, -13, -15]) + (countLit q [-18, -20, -22, -23, -24, -27, -30]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -6, -10, -11, -13, -15]) (l₂ := [-18, -20, -22, -23, -24, -27, -30])
  have hm := merge_two (literal (valuationOf q) (1416)) (literal (valuationOf q) (1437)) (literal (valuationOf q) (1447)) (countLit q [-2, -5, -6, -10, -11, -13, -15]) (countLit q [-18, -20, -22, -23, -24, -27, -30]) (count1441 q) 3 4 (meaning1416 q) (meaning1437 q) (meaning1447 q) hs
  change valuationOf q 1416 = false ∨ valuationOf q 1437 = false ∨ valuationOf q 1447 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause391 (q : Snake 81) (h : Conditions q) : valuation q 1416 = false ∨ valuation q 1437 = false ∨ valuation q 1447 = true := counterClause391 (baseVal q)

theorem counterClause392 (q : Nat → Bool) : valuationOf q 35 = true ∨ valuationOf q 1455 = true := by
  have hs : count1455 q = (countLit q [-34]) + (countLit q [-35]) := List.countP_append (p := literal q) (l₁ := [-34]) (l₂ := [-35])
  have hm := merge_right (literal (valuationOf q) (-35)) (literal (valuationOf q) (1455)) (countLit q [-34]) (countLit q [-35]) (count1455 q) 1 (meaningNeg35 q) (meaning1455 q) hs
  change (! (valuationOf q 35)) = false ∨ valuationOf q 1455 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause392 (q : Snake 81) (h : Conditions q) : valuation q 35 = true ∨ valuation q 1455 = true := counterClause392 (baseVal q)

theorem counterClause393 (q : Nat → Bool) : valuationOf q 34 = true ∨ valuationOf q 1455 = true := by
  have hs : count1455 q = (countLit q [-34]) + (countLit q [-35]) := List.countP_append (p := literal q) (l₁ := [-34]) (l₂ := [-35])
  have hm := merge_left (literal (valuationOf q) (-34)) (literal (valuationOf q) (1455)) (countLit q [-34]) (countLit q [-35]) (count1455 q) 1 (meaningNeg34 q) (meaning1455 q) hs
  change (! (valuationOf q 34)) = false ∨ valuationOf q 1455 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause393 (q : Snake 81) (h : Conditions q) : valuation q 34 = true ∨ valuation q 1455 = true := counterClause393 (baseVal q)

theorem counterClause394 (q : Nat → Bool) : valuationOf q 34 = true ∨ valuationOf q 35 = true ∨ valuationOf q 1456 = true := by
  have hs : count1455 q = (countLit q [-34]) + (countLit q [-35]) := List.countP_append (p := literal q) (l₁ := [-34]) (l₂ := [-35])
  have hm := merge_two (literal (valuationOf q) (-34)) (literal (valuationOf q) (-35)) (literal (valuationOf q) (1456)) (countLit q [-34]) (countLit q [-35]) (count1455 q) 1 1 (meaningNeg34 q) (meaningNeg35 q) (meaning1456 q) hs
  change (! (valuationOf q 34)) = false ∨ (! (valuationOf q 35)) = false ∨ valuationOf q 1456 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause394 (q : Snake 81) (h : Conditions q) : valuation q 34 = true ∨ valuation q 35 = true ∨ valuation q 1456 = true := counterClause394 (baseVal q)

theorem counterClause395 (q : Nat → Bool) : valuationOf q 1455 = false ∨ valuationOf q 1457 = true := by
  have hs : count1457 q = (countLit q [-33]) + (countLit q [-34, -35]) := List.countP_append (p := literal q) (l₁ := [-33]) (l₂ := [-34, -35])
  have hm := merge_right (literal (valuationOf q) (1455)) (literal (valuationOf q) (1457)) (countLit q [-33]) (countLit q [-34, -35]) (count1457 q) 1 (meaning1455 q) (meaning1457 q) hs
  change valuationOf q 1455 = false ∨ valuationOf q 1457 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause395 (q : Snake 81) (h : Conditions q) : valuation q 1455 = false ∨ valuation q 1457 = true := counterClause395 (baseVal q)

theorem counterClause396 (q : Nat → Bool) : valuationOf q 1456 = false ∨ valuationOf q 1458 = true := by
  have hs : count1457 q = (countLit q [-33]) + (countLit q [-34, -35]) := List.countP_append (p := literal q) (l₁ := [-33]) (l₂ := [-34, -35])
  have hm := merge_right (literal (valuationOf q) (1456)) (literal (valuationOf q) (1458)) (countLit q [-33]) (countLit q [-34, -35]) (count1457 q) 2 (meaning1456 q) (meaning1458 q) hs
  change valuationOf q 1456 = false ∨ valuationOf q 1458 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause396 (q : Snake 81) (h : Conditions q) : valuation q 1456 = false ∨ valuation q 1458 = true := counterClause396 (baseVal q)

theorem counterClause397 (q : Nat → Bool) : valuationOf q 33 = true ∨ valuationOf q 1457 = true := by
  have hs : count1457 q = (countLit q [-33]) + (countLit q [-34, -35]) := List.countP_append (p := literal q) (l₁ := [-33]) (l₂ := [-34, -35])
  have hm := merge_left (literal (valuationOf q) (-33)) (literal (valuationOf q) (1457)) (countLit q [-33]) (countLit q [-34, -35]) (count1457 q) 1 (meaningNeg33 q) (meaning1457 q) hs
  change (! (valuationOf q 33)) = false ∨ valuationOf q 1457 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause397 (q : Snake 81) (h : Conditions q) : valuation q 33 = true ∨ valuation q 1457 = true := counterClause397 (baseVal q)

theorem counterClause398 (q : Nat → Bool) : valuationOf q 33 = true ∨ valuationOf q 1455 = false ∨ valuationOf q 1458 = true := by
  have hs : count1457 q = (countLit q [-33]) + (countLit q [-34, -35]) := List.countP_append (p := literal q) (l₁ := [-33]) (l₂ := [-34, -35])
  have hm := merge_two (literal (valuationOf q) (-33)) (literal (valuationOf q) (1455)) (literal (valuationOf q) (1458)) (countLit q [-33]) (countLit q [-34, -35]) (count1457 q) 1 1 (meaningNeg33 q) (meaning1455 q) (meaning1458 q) hs
  change (! (valuationOf q 33)) = false ∨ valuationOf q 1455 = false ∨ valuationOf q 1458 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause398 (q : Snake 81) (h : Conditions q) : valuation q 33 = true ∨ valuation q 1455 = false ∨ valuation q 1458 = true := counterClause398 (baseVal q)

theorem counterClause399 (q : Nat → Bool) : valuationOf q 33 = true ∨ valuationOf q 1456 = false ∨ valuationOf q 1459 = true := by
  have hs : count1457 q = (countLit q [-33]) + (countLit q [-34, -35]) := List.countP_append (p := literal q) (l₁ := [-33]) (l₂ := [-34, -35])
  have hm := merge_two (literal (valuationOf q) (-33)) (literal (valuationOf q) (1456)) (literal (valuationOf q) (1459)) (countLit q [-33]) (countLit q [-34, -35]) (count1457 q) 1 2 (meaningNeg33 q) (meaning1456 q) (meaning1459 q) hs
  change (! (valuationOf q 33)) = false ∨ valuationOf q 1456 = false ∨ valuationOf q 1459 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause399 (q : Snake 81) (h : Conditions q) : valuation q 33 = true ∨ valuation q 1456 = false ∨ valuation q 1459 = true := counterClause399 (baseVal q)

theorem counterClause400 (q : Nat → Bool) : valuationOf q 39 = true ∨ valuationOf q 1460 = true := by
  have hs : count1460 q = (countLit q [-37]) + (countLit q [-39]) := List.countP_append (p := literal q) (l₁ := [-37]) (l₂ := [-39])
  have hm := merge_right (literal (valuationOf q) (-39)) (literal (valuationOf q) (1460)) (countLit q [-37]) (countLit q [-39]) (count1460 q) 1 (meaningNeg39 q) (meaning1460 q) hs
  change (! (valuationOf q 39)) = false ∨ valuationOf q 1460 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause400 (q : Snake 81) (h : Conditions q) : valuation q 39 = true ∨ valuation q 1460 = true := counterClause400 (baseVal q)

theorem counterClause401 (q : Nat → Bool) : valuationOf q 37 = true ∨ valuationOf q 1460 = true := by
  have hs : count1460 q = (countLit q [-37]) + (countLit q [-39]) := List.countP_append (p := literal q) (l₁ := [-37]) (l₂ := [-39])
  have hm := merge_left (literal (valuationOf q) (-37)) (literal (valuationOf q) (1460)) (countLit q [-37]) (countLit q [-39]) (count1460 q) 1 (meaningNeg37 q) (meaning1460 q) hs
  change (! (valuationOf q 37)) = false ∨ valuationOf q 1460 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause401 (q : Snake 81) (h : Conditions q) : valuation q 37 = true ∨ valuation q 1460 = true := counterClause401 (baseVal q)

theorem counterClause402 (q : Nat → Bool) : valuationOf q 37 = true ∨ valuationOf q 39 = true ∨ valuationOf q 1461 = true := by
  have hs : count1460 q = (countLit q [-37]) + (countLit q [-39]) := List.countP_append (p := literal q) (l₁ := [-37]) (l₂ := [-39])
  have hm := merge_two (literal (valuationOf q) (-37)) (literal (valuationOf q) (-39)) (literal (valuationOf q) (1461)) (countLit q [-37]) (countLit q [-39]) (count1460 q) 1 1 (meaningNeg37 q) (meaningNeg39 q) (meaning1461 q) hs
  change (! (valuationOf q 37)) = false ∨ (! (valuationOf q 39)) = false ∨ valuationOf q 1461 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause402 (q : Snake 81) (h : Conditions q) : valuation q 37 = true ∨ valuation q 39 = true ∨ valuation q 1461 = true := counterClause402 (baseVal q)

theorem counterClause403 (q : Nat → Bool) : valuationOf q 43 = true ∨ valuationOf q 1462 = true := by
  have hs : count1462 q = (countLit q [-42]) + (countLit q [-43]) := List.countP_append (p := literal q) (l₁ := [-42]) (l₂ := [-43])
  have hm := merge_right (literal (valuationOf q) (-43)) (literal (valuationOf q) (1462)) (countLit q [-42]) (countLit q [-43]) (count1462 q) 1 (meaningNeg43 q) (meaning1462 q) hs
  change (! (valuationOf q 43)) = false ∨ valuationOf q 1462 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause403 (q : Snake 81) (h : Conditions q) : valuation q 43 = true ∨ valuation q 1462 = true := counterClause403 (baseVal q)

theorem counterClause404 (q : Nat → Bool) : valuationOf q 42 = true ∨ valuationOf q 1462 = true := by
  have hs : count1462 q = (countLit q [-42]) + (countLit q [-43]) := List.countP_append (p := literal q) (l₁ := [-42]) (l₂ := [-43])
  have hm := merge_left (literal (valuationOf q) (-42)) (literal (valuationOf q) (1462)) (countLit q [-42]) (countLit q [-43]) (count1462 q) 1 (meaningNeg42 q) (meaning1462 q) hs
  change (! (valuationOf q 42)) = false ∨ valuationOf q 1462 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause404 (q : Snake 81) (h : Conditions q) : valuation q 42 = true ∨ valuation q 1462 = true := counterClause404 (baseVal q)

theorem counterClause405 (q : Nat → Bool) : valuationOf q 42 = true ∨ valuationOf q 43 = true ∨ valuationOf q 1463 = true := by
  have hs : count1462 q = (countLit q [-42]) + (countLit q [-43]) := List.countP_append (p := literal q) (l₁ := [-42]) (l₂ := [-43])
  have hm := merge_two (literal (valuationOf q) (-42)) (literal (valuationOf q) (-43)) (literal (valuationOf q) (1463)) (countLit q [-42]) (countLit q [-43]) (count1462 q) 1 1 (meaningNeg42 q) (meaningNeg43 q) (meaning1463 q) hs
  change (! (valuationOf q 42)) = false ∨ (! (valuationOf q 43)) = false ∨ valuationOf q 1463 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause405 (q : Snake 81) (h : Conditions q) : valuation q 42 = true ∨ valuation q 43 = true ∨ valuation q 1463 = true := counterClause405 (baseVal q)

theorem counterClause406 (q : Nat → Bool) : valuationOf q 1462 = false ∨ valuationOf q 1464 = true := by
  have hs : count1464 q = (countLit q [-37, -39]) + (countLit q [-42, -43]) := List.countP_append (p := literal q) (l₁ := [-37, -39]) (l₂ := [-42, -43])
  have hm := merge_right (literal (valuationOf q) (1462)) (literal (valuationOf q) (1464)) (countLit q [-37, -39]) (countLit q [-42, -43]) (count1464 q) 1 (meaning1462 q) (meaning1464 q) hs
  change valuationOf q 1462 = false ∨ valuationOf q 1464 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause406 (q : Snake 81) (h : Conditions q) : valuation q 1462 = false ∨ valuation q 1464 = true := counterClause406 (baseVal q)

theorem counterClause407 (q : Nat → Bool) : valuationOf q 1463 = false ∨ valuationOf q 1465 = true := by
  have hs : count1464 q = (countLit q [-37, -39]) + (countLit q [-42, -43]) := List.countP_append (p := literal q) (l₁ := [-37, -39]) (l₂ := [-42, -43])
  have hm := merge_right (literal (valuationOf q) (1463)) (literal (valuationOf q) (1465)) (countLit q [-37, -39]) (countLit q [-42, -43]) (count1464 q) 2 (meaning1463 q) (meaning1465 q) hs
  change valuationOf q 1463 = false ∨ valuationOf q 1465 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause407 (q : Snake 81) (h : Conditions q) : valuation q 1463 = false ∨ valuation q 1465 = true := counterClause407 (baseVal q)

theorem counterClause408 (q : Nat → Bool) : valuationOf q 1460 = false ∨ valuationOf q 1464 = true := by
  have hs : count1464 q = (countLit q [-37, -39]) + (countLit q [-42, -43]) := List.countP_append (p := literal q) (l₁ := [-37, -39]) (l₂ := [-42, -43])
  have hm := merge_left (literal (valuationOf q) (1460)) (literal (valuationOf q) (1464)) (countLit q [-37, -39]) (countLit q [-42, -43]) (count1464 q) 1 (meaning1460 q) (meaning1464 q) hs
  change valuationOf q 1460 = false ∨ valuationOf q 1464 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause408 (q : Snake 81) (h : Conditions q) : valuation q 1460 = false ∨ valuation q 1464 = true := counterClause408 (baseVal q)

theorem counterClause409 (q : Nat → Bool) : valuationOf q 1460 = false ∨ valuationOf q 1462 = false ∨ valuationOf q 1465 = true := by
  have hs : count1464 q = (countLit q [-37, -39]) + (countLit q [-42, -43]) := List.countP_append (p := literal q) (l₁ := [-37, -39]) (l₂ := [-42, -43])
  have hm := merge_two (literal (valuationOf q) (1460)) (literal (valuationOf q) (1462)) (literal (valuationOf q) (1465)) (countLit q [-37, -39]) (countLit q [-42, -43]) (count1464 q) 1 1 (meaning1460 q) (meaning1462 q) (meaning1465 q) hs
  change valuationOf q 1460 = false ∨ valuationOf q 1462 = false ∨ valuationOf q 1465 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause409 (q : Snake 81) (h : Conditions q) : valuation q 1460 = false ∨ valuation q 1462 = false ∨ valuation q 1465 = true := counterClause409 (baseVal q)

theorem counterClause410 (q : Nat → Bool) : valuationOf q 1460 = false ∨ valuationOf q 1463 = false ∨ valuationOf q 1466 = true := by
  have hs : count1464 q = (countLit q [-37, -39]) + (countLit q [-42, -43]) := List.countP_append (p := literal q) (l₁ := [-37, -39]) (l₂ := [-42, -43])
  have hm := merge_two (literal (valuationOf q) (1460)) (literal (valuationOf q) (1463)) (literal (valuationOf q) (1466)) (countLit q [-37, -39]) (countLit q [-42, -43]) (count1464 q) 1 2 (meaning1460 q) (meaning1463 q) (meaning1466 q) hs
  change valuationOf q 1460 = false ∨ valuationOf q 1463 = false ∨ valuationOf q 1466 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause410 (q : Snake 81) (h : Conditions q) : valuation q 1460 = false ∨ valuation q 1463 = false ∨ valuation q 1466 = true := counterClause410 (baseVal q)

theorem counterClause411 (q : Nat → Bool) : valuationOf q 1461 = false ∨ valuationOf q 1465 = true := by
  have hs : count1464 q = (countLit q [-37, -39]) + (countLit q [-42, -43]) := List.countP_append (p := literal q) (l₁ := [-37, -39]) (l₂ := [-42, -43])
  have hm := merge_left (literal (valuationOf q) (1461)) (literal (valuationOf q) (1465)) (countLit q [-37, -39]) (countLit q [-42, -43]) (count1464 q) 2 (meaning1461 q) (meaning1465 q) hs
  change valuationOf q 1461 = false ∨ valuationOf q 1465 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause411 (q : Snake 81) (h : Conditions q) : valuation q 1461 = false ∨ valuation q 1465 = true := counterClause411 (baseVal q)

theorem counterClause412 (q : Nat → Bool) : valuationOf q 1464 = false ∨ valuationOf q 1468 = true := by
  have hs : count1468 q = (countLit q [-33, -34, -35]) + (countLit q [-37, -39, -42, -43]) := List.countP_append (p := literal q) (l₁ := [-33, -34, -35]) (l₂ := [-37, -39, -42, -43])
  have hm := merge_right (literal (valuationOf q) (1464)) (literal (valuationOf q) (1468)) (countLit q [-33, -34, -35]) (countLit q [-37, -39, -42, -43]) (count1468 q) 1 (meaning1464 q) (meaning1468 q) hs
  change valuationOf q 1464 = false ∨ valuationOf q 1468 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause412 (q : Snake 81) (h : Conditions q) : valuation q 1464 = false ∨ valuation q 1468 = true := counterClause412 (baseVal q)

theorem counterClause413 (q : Nat → Bool) : valuationOf q 1465 = false ∨ valuationOf q 1469 = true := by
  have hs : count1468 q = (countLit q [-33, -34, -35]) + (countLit q [-37, -39, -42, -43]) := List.countP_append (p := literal q) (l₁ := [-33, -34, -35]) (l₂ := [-37, -39, -42, -43])
  have hm := merge_right (literal (valuationOf q) (1465)) (literal (valuationOf q) (1469)) (countLit q [-33, -34, -35]) (countLit q [-37, -39, -42, -43]) (count1468 q) 2 (meaning1465 q) (meaning1469 q) hs
  change valuationOf q 1465 = false ∨ valuationOf q 1469 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause413 (q : Snake 81) (h : Conditions q) : valuation q 1465 = false ∨ valuation q 1469 = true := counterClause413 (baseVal q)

theorem counterClause414 (q : Nat → Bool) : valuationOf q 1457 = false ∨ valuationOf q 1464 = false ∨ valuationOf q 1469 = true := by
  have hs : count1468 q = (countLit q [-33, -34, -35]) + (countLit q [-37, -39, -42, -43]) := List.countP_append (p := literal q) (l₁ := [-33, -34, -35]) (l₂ := [-37, -39, -42, -43])
  have hm := merge_two (literal (valuationOf q) (1457)) (literal (valuationOf q) (1464)) (literal (valuationOf q) (1469)) (countLit q [-33, -34, -35]) (countLit q [-37, -39, -42, -43]) (count1468 q) 1 1 (meaning1457 q) (meaning1464 q) (meaning1469 q) hs
  change valuationOf q 1457 = false ∨ valuationOf q 1464 = false ∨ valuationOf q 1469 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause414 (q : Snake 81) (h : Conditions q) : valuation q 1457 = false ∨ valuation q 1464 = false ∨ valuation q 1469 = true := counterClause414 (baseVal q)

theorem counterClause415 (q : Nat → Bool) : valuationOf q 1457 = false ∨ valuationOf q 1465 = false ∨ valuationOf q 1470 = true := by
  have hs : count1468 q = (countLit q [-33, -34, -35]) + (countLit q [-37, -39, -42, -43]) := List.countP_append (p := literal q) (l₁ := [-33, -34, -35]) (l₂ := [-37, -39, -42, -43])
  have hm := merge_two (literal (valuationOf q) (1457)) (literal (valuationOf q) (1465)) (literal (valuationOf q) (1470)) (countLit q [-33, -34, -35]) (countLit q [-37, -39, -42, -43]) (count1468 q) 1 2 (meaning1457 q) (meaning1465 q) (meaning1470 q) hs
  change valuationOf q 1457 = false ∨ valuationOf q 1465 = false ∨ valuationOf q 1470 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause415 (q : Snake 81) (h : Conditions q) : valuation q 1457 = false ∨ valuation q 1465 = false ∨ valuation q 1470 = true := counterClause415 (baseVal q)

theorem counterClause416 (q : Nat → Bool) : valuationOf q 1457 = false ∨ valuationOf q 1466 = false ∨ valuationOf q 1471 = true := by
  have hs : count1468 q = (countLit q [-33, -34, -35]) + (countLit q [-37, -39, -42, -43]) := List.countP_append (p := literal q) (l₁ := [-33, -34, -35]) (l₂ := [-37, -39, -42, -43])
  have hm := merge_two (literal (valuationOf q) (1457)) (literal (valuationOf q) (1466)) (literal (valuationOf q) (1471)) (countLit q [-33, -34, -35]) (countLit q [-37, -39, -42, -43]) (count1468 q) 1 3 (meaning1457 q) (meaning1466 q) (meaning1471 q) hs
  change valuationOf q 1457 = false ∨ valuationOf q 1466 = false ∨ valuationOf q 1471 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause416 (q : Snake 81) (h : Conditions q) : valuation q 1457 = false ∨ valuation q 1466 = false ∨ valuation q 1471 = true := counterClause416 (baseVal q)

theorem block12 (q : Snake 81) (h : Conditions q) : B112E058.Block12 (valuation q) :=
  ⟨clause385 q h, clause386 q h, clause387 q h, clause388 q h, clause389 q h, clause390 q h, clause391 q h, clause392 q h, clause393 q h, clause394 q h, clause395 q h, clause396 q h, clause397 q h, clause398 q h, clause399 q h, clause400 q h, clause401 q h, clause402 q h, clause403 q h, clause404 q h, clause405 q h, clause406 q h, clause407 q h, clause408 q h, clause409 q h, clause410 q h, clause411 q h, clause412 q h, clause413 q h, clause414 q h, clause415 q h, clause416 q h⟩

end
end Snake9.Regrowth.E112058
