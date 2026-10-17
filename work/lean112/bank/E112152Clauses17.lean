import E112152Semantics
import B112E152Inputs
namespace Snake9.Regrowth.E112152
noncomputable section
local instance blockDec17 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause545 (q : Nat → Bool) : valuationOf q 356 = false ∨ valuationOf q 476 = true := by
  have hs : count475 q = (countLit q [121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179]) + (countLit q [180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240]) := List.countP_append (p := literal q) (l₁ := [121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179]) (l₂ := [180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240])
  have hm := merge_left (literal (valuationOf q) (356)) (literal (valuationOf q) (476)) (countLit q [121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179]) (countLit q [180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240]) (count475 q) 2 (meaning356 q) (meaning476 q) hs
  change valuationOf q 356 = false ∨ valuationOf q 476 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause545 (q : Snake 81) (h : Conditions q) : valuation q 356 = false ∨ valuation q 476 = true := counterClause545 (baseVal q)

theorem clause546 (q : Snake 81) (h : Conditions q) : valuation q 476 = false := by
  rw [value476]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have he : count475 (baseVal q) = (others.filter (fun v => decide (BallClauseLogic.Endpoint q v))).length := by
    rw [← List.countP_eq_length_filter]
    rfl
  have hb := other_count_bound q h
  rw [he]
  omega

theorem counterClause547 (q : Nat → Bool) : valuationOf q 6 = true ∨ valuationOf q 1457 = true := by
  have hs : count1457 q = (countLit q [-4]) + (countLit q [-6]) := List.countP_append (p := literal q) (l₁ := [-4]) (l₂ := [-6])
  have hm := merge_right (literal (valuationOf q) (-6)) (literal (valuationOf q) (1457)) (countLit q [-4]) (countLit q [-6]) (count1457 q) 1 (meaningNeg6 q) (meaning1457 q) hs
  change (! (valuationOf q 6)) = false ∨ valuationOf q 1457 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause547 (q : Snake 81) (h : Conditions q) : valuation q 6 = true ∨ valuation q 1457 = true := counterClause547 (baseVal q)

theorem counterClause548 (q : Nat → Bool) : valuationOf q 4 = true ∨ valuationOf q 1457 = true := by
  have hs : count1457 q = (countLit q [-4]) + (countLit q [-6]) := List.countP_append (p := literal q) (l₁ := [-4]) (l₂ := [-6])
  have hm := merge_left (literal (valuationOf q) (-4)) (literal (valuationOf q) (1457)) (countLit q [-4]) (countLit q [-6]) (count1457 q) 1 (meaningNeg4 q) (meaning1457 q) hs
  change (! (valuationOf q 4)) = false ∨ valuationOf q 1457 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause548 (q : Snake 81) (h : Conditions q) : valuation q 4 = true ∨ valuation q 1457 = true := counterClause548 (baseVal q)

theorem counterClause549 (q : Nat → Bool) : valuationOf q 4 = true ∨ valuationOf q 6 = true ∨ valuationOf q 1458 = true := by
  have hs : count1457 q = (countLit q [-4]) + (countLit q [-6]) := List.countP_append (p := literal q) (l₁ := [-4]) (l₂ := [-6])
  have hm := merge_two (literal (valuationOf q) (-4)) (literal (valuationOf q) (-6)) (literal (valuationOf q) (1458)) (countLit q [-4]) (countLit q [-6]) (count1457 q) 1 1 (meaningNeg4 q) (meaningNeg6 q) (meaning1458 q) hs
  change (! (valuationOf q 4)) = false ∨ (! (valuationOf q 6)) = false ∨ valuationOf q 1458 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause549 (q : Snake 81) (h : Conditions q) : valuation q 4 = true ∨ valuation q 6 = true ∨ valuation q 1458 = true := counterClause549 (baseVal q)

theorem counterClause550 (q : Nat → Bool) : valuationOf q 3 = true ∨ valuationOf q 1459 = true := by
  have hs : count1459 q = (countLit q [-3]) + (countLit q [-4, -6]) := List.countP_append (p := literal q) (l₁ := [-3]) (l₂ := [-4, -6])
  have hm := merge_left (literal (valuationOf q) (-3)) (literal (valuationOf q) (1459)) (countLit q [-3]) (countLit q [-4, -6]) (count1459 q) 1 (meaningNeg3 q) (meaning1459 q) hs
  change (! (valuationOf q 3)) = false ∨ valuationOf q 1459 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause550 (q : Snake 81) (h : Conditions q) : valuation q 3 = true ∨ valuation q 1459 = true := counterClause550 (baseVal q)

theorem counterClause551 (q : Nat → Bool) : valuationOf q 3 = true ∨ valuationOf q 1457 = false ∨ valuationOf q 1460 = true := by
  have hs : count1459 q = (countLit q [-3]) + (countLit q [-4, -6]) := List.countP_append (p := literal q) (l₁ := [-3]) (l₂ := [-4, -6])
  have hm := merge_two (literal (valuationOf q) (-3)) (literal (valuationOf q) (1457)) (literal (valuationOf q) (1460)) (countLit q [-3]) (countLit q [-4, -6]) (count1459 q) 1 1 (meaningNeg3 q) (meaning1457 q) (meaning1460 q) hs
  change (! (valuationOf q 3)) = false ∨ valuationOf q 1457 = false ∨ valuationOf q 1460 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause551 (q : Snake 81) (h : Conditions q) : valuation q 3 = true ∨ valuation q 1457 = false ∨ valuation q 1460 = true := counterClause551 (baseVal q)

theorem counterClause552 (q : Nat → Bool) : valuationOf q 3 = true ∨ valuationOf q 1458 = false ∨ valuationOf q 1461 = true := by
  have hs : count1459 q = (countLit q [-3]) + (countLit q [-4, -6]) := List.countP_append (p := literal q) (l₁ := [-3]) (l₂ := [-4, -6])
  have hm := merge_two (literal (valuationOf q) (-3)) (literal (valuationOf q) (1458)) (literal (valuationOf q) (1461)) (countLit q [-3]) (countLit q [-4, -6]) (count1459 q) 1 2 (meaningNeg3 q) (meaning1458 q) (meaning1461 q) hs
  change (! (valuationOf q 3)) = false ∨ valuationOf q 1458 = false ∨ valuationOf q 1461 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause552 (q : Snake 81) (h : Conditions q) : valuation q 3 = true ∨ valuation q 1458 = false ∨ valuation q 1461 = true := counterClause552 (baseVal q)

theorem counterClause553 (q : Nat → Bool) : valuationOf q 11 = true ∨ valuationOf q 1462 = true := by
  have hs : count1462 q = (countLit q [-8]) + (countLit q [-11]) := List.countP_append (p := literal q) (l₁ := [-8]) (l₂ := [-11])
  have hm := merge_right (literal (valuationOf q) (-11)) (literal (valuationOf q) (1462)) (countLit q [-8]) (countLit q [-11]) (count1462 q) 1 (meaningNeg11 q) (meaning1462 q) hs
  change (! (valuationOf q 11)) = false ∨ valuationOf q 1462 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause553 (q : Snake 81) (h : Conditions q) : valuation q 11 = true ∨ valuation q 1462 = true := counterClause553 (baseVal q)

theorem counterClause554 (q : Nat → Bool) : valuationOf q 8 = true ∨ valuationOf q 1462 = true := by
  have hs : count1462 q = (countLit q [-8]) + (countLit q [-11]) := List.countP_append (p := literal q) (l₁ := [-8]) (l₂ := [-11])
  have hm := merge_left (literal (valuationOf q) (-8)) (literal (valuationOf q) (1462)) (countLit q [-8]) (countLit q [-11]) (count1462 q) 1 (meaningNeg8 q) (meaning1462 q) hs
  change (! (valuationOf q 8)) = false ∨ valuationOf q 1462 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause554 (q : Snake 81) (h : Conditions q) : valuation q 8 = true ∨ valuation q 1462 = true := counterClause554 (baseVal q)

theorem counterClause555 (q : Nat → Bool) : valuationOf q 8 = true ∨ valuationOf q 11 = true ∨ valuationOf q 1463 = true := by
  have hs : count1462 q = (countLit q [-8]) + (countLit q [-11]) := List.countP_append (p := literal q) (l₁ := [-8]) (l₂ := [-11])
  have hm := merge_two (literal (valuationOf q) (-8)) (literal (valuationOf q) (-11)) (literal (valuationOf q) (1463)) (countLit q [-8]) (countLit q [-11]) (count1462 q) 1 1 (meaningNeg8 q) (meaningNeg11 q) (meaning1463 q) hs
  change (! (valuationOf q 8)) = false ∨ (! (valuationOf q 11)) = false ∨ valuationOf q 1463 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause555 (q : Snake 81) (h : Conditions q) : valuation q 8 = true ∨ valuation q 11 = true ∨ valuation q 1463 = true := counterClause555 (baseVal q)

theorem counterClause556 (q : Nat → Bool) : valuationOf q 14 = true ∨ valuationOf q 1464 = true := by
  have hs : count1464 q = (countLit q [-13]) + (countLit q [-14]) := List.countP_append (p := literal q) (l₁ := [-13]) (l₂ := [-14])
  have hm := merge_right (literal (valuationOf q) (-14)) (literal (valuationOf q) (1464)) (countLit q [-13]) (countLit q [-14]) (count1464 q) 1 (meaningNeg14 q) (meaning1464 q) hs
  change (! (valuationOf q 14)) = false ∨ valuationOf q 1464 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause556 (q : Snake 81) (h : Conditions q) : valuation q 14 = true ∨ valuation q 1464 = true := counterClause556 (baseVal q)

theorem counterClause557 (q : Nat → Bool) : valuationOf q 13 = true ∨ valuationOf q 1464 = true := by
  have hs : count1464 q = (countLit q [-13]) + (countLit q [-14]) := List.countP_append (p := literal q) (l₁ := [-13]) (l₂ := [-14])
  have hm := merge_left (literal (valuationOf q) (-13)) (literal (valuationOf q) (1464)) (countLit q [-13]) (countLit q [-14]) (count1464 q) 1 (meaningNeg13 q) (meaning1464 q) hs
  change (! (valuationOf q 13)) = false ∨ valuationOf q 1464 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause557 (q : Snake 81) (h : Conditions q) : valuation q 13 = true ∨ valuation q 1464 = true := counterClause557 (baseVal q)

theorem counterClause558 (q : Nat → Bool) : valuationOf q 13 = true ∨ valuationOf q 14 = true ∨ valuationOf q 1465 = true := by
  have hs : count1464 q = (countLit q [-13]) + (countLit q [-14]) := List.countP_append (p := literal q) (l₁ := [-13]) (l₂ := [-14])
  have hm := merge_two (literal (valuationOf q) (-13)) (literal (valuationOf q) (-14)) (literal (valuationOf q) (1465)) (countLit q [-13]) (countLit q [-14]) (count1464 q) 1 1 (meaningNeg13 q) (meaningNeg14 q) (meaning1465 q) hs
  change (! (valuationOf q 13)) = false ∨ (! (valuationOf q 14)) = false ∨ valuationOf q 1465 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause558 (q : Snake 81) (h : Conditions q) : valuation q 13 = true ∨ valuation q 14 = true ∨ valuation q 1465 = true := counterClause558 (baseVal q)

theorem counterClause559 (q : Nat → Bool) : valuationOf q 1464 = false ∨ valuationOf q 1466 = true := by
  have hs : count1466 q = (countLit q [-8, -11]) + (countLit q [-13, -14]) := List.countP_append (p := literal q) (l₁ := [-8, -11]) (l₂ := [-13, -14])
  have hm := merge_right (literal (valuationOf q) (1464)) (literal (valuationOf q) (1466)) (countLit q [-8, -11]) (countLit q [-13, -14]) (count1466 q) 1 (meaning1464 q) (meaning1466 q) hs
  change valuationOf q 1464 = false ∨ valuationOf q 1466 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause559 (q : Snake 81) (h : Conditions q) : valuation q 1464 = false ∨ valuation q 1466 = true := counterClause559 (baseVal q)

theorem counterClause560 (q : Nat → Bool) : valuationOf q 1465 = false ∨ valuationOf q 1467 = true := by
  have hs : count1466 q = (countLit q [-8, -11]) + (countLit q [-13, -14]) := List.countP_append (p := literal q) (l₁ := [-8, -11]) (l₂ := [-13, -14])
  have hm := merge_right (literal (valuationOf q) (1465)) (literal (valuationOf q) (1467)) (countLit q [-8, -11]) (countLit q [-13, -14]) (count1466 q) 2 (meaning1465 q) (meaning1467 q) hs
  change valuationOf q 1465 = false ∨ valuationOf q 1467 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause560 (q : Snake 81) (h : Conditions q) : valuation q 1465 = false ∨ valuation q 1467 = true := counterClause560 (baseVal q)

theorem counterClause561 (q : Nat → Bool) : valuationOf q 1462 = false ∨ valuationOf q 1466 = true := by
  have hs : count1466 q = (countLit q [-8, -11]) + (countLit q [-13, -14]) := List.countP_append (p := literal q) (l₁ := [-8, -11]) (l₂ := [-13, -14])
  have hm := merge_left (literal (valuationOf q) (1462)) (literal (valuationOf q) (1466)) (countLit q [-8, -11]) (countLit q [-13, -14]) (count1466 q) 1 (meaning1462 q) (meaning1466 q) hs
  change valuationOf q 1462 = false ∨ valuationOf q 1466 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause561 (q : Snake 81) (h : Conditions q) : valuation q 1462 = false ∨ valuation q 1466 = true := counterClause561 (baseVal q)

theorem counterClause562 (q : Nat → Bool) : valuationOf q 1462 = false ∨ valuationOf q 1464 = false ∨ valuationOf q 1467 = true := by
  have hs : count1466 q = (countLit q [-8, -11]) + (countLit q [-13, -14]) := List.countP_append (p := literal q) (l₁ := [-8, -11]) (l₂ := [-13, -14])
  have hm := merge_two (literal (valuationOf q) (1462)) (literal (valuationOf q) (1464)) (literal (valuationOf q) (1467)) (countLit q [-8, -11]) (countLit q [-13, -14]) (count1466 q) 1 1 (meaning1462 q) (meaning1464 q) (meaning1467 q) hs
  change valuationOf q 1462 = false ∨ valuationOf q 1464 = false ∨ valuationOf q 1467 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause562 (q : Snake 81) (h : Conditions q) : valuation q 1462 = false ∨ valuation q 1464 = false ∨ valuation q 1467 = true := counterClause562 (baseVal q)

theorem counterClause563 (q : Nat → Bool) : valuationOf q 1462 = false ∨ valuationOf q 1465 = false ∨ valuationOf q 1468 = true := by
  have hs : count1466 q = (countLit q [-8, -11]) + (countLit q [-13, -14]) := List.countP_append (p := literal q) (l₁ := [-8, -11]) (l₂ := [-13, -14])
  have hm := merge_two (literal (valuationOf q) (1462)) (literal (valuationOf q) (1465)) (literal (valuationOf q) (1468)) (countLit q [-8, -11]) (countLit q [-13, -14]) (count1466 q) 1 2 (meaning1462 q) (meaning1465 q) (meaning1468 q) hs
  change valuationOf q 1462 = false ∨ valuationOf q 1465 = false ∨ valuationOf q 1468 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause563 (q : Snake 81) (h : Conditions q) : valuation q 1462 = false ∨ valuation q 1465 = false ∨ valuation q 1468 = true := counterClause563 (baseVal q)

theorem counterClause564 (q : Nat → Bool) : valuationOf q 1463 = false ∨ valuationOf q 1467 = true := by
  have hs : count1466 q = (countLit q [-8, -11]) + (countLit q [-13, -14]) := List.countP_append (p := literal q) (l₁ := [-8, -11]) (l₂ := [-13, -14])
  have hm := merge_left (literal (valuationOf q) (1463)) (literal (valuationOf q) (1467)) (countLit q [-8, -11]) (countLit q [-13, -14]) (count1466 q) 2 (meaning1463 q) (meaning1467 q) hs
  change valuationOf q 1463 = false ∨ valuationOf q 1467 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause564 (q : Snake 81) (h : Conditions q) : valuation q 1463 = false ∨ valuation q 1467 = true := counterClause564 (baseVal q)

theorem counterClause565 (q : Nat → Bool) : valuationOf q 1459 = false ∨ valuationOf q 1466 = false ∨ valuationOf q 1471 = true := by
  have hs : count1470 q = (countLit q [-3, -4, -6]) + (countLit q [-8, -11, -13, -14]) := List.countP_append (p := literal q) (l₁ := [-3, -4, -6]) (l₂ := [-8, -11, -13, -14])
  have hm := merge_two (literal (valuationOf q) (1459)) (literal (valuationOf q) (1466)) (literal (valuationOf q) (1471)) (countLit q [-3, -4, -6]) (countLit q [-8, -11, -13, -14]) (count1470 q) 1 1 (meaning1459 q) (meaning1466 q) (meaning1471 q) hs
  change valuationOf q 1459 = false ∨ valuationOf q 1466 = false ∨ valuationOf q 1471 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause565 (q : Snake 81) (h : Conditions q) : valuation q 1459 = false ∨ valuation q 1466 = false ∨ valuation q 1471 = true := counterClause565 (baseVal q)

theorem counterClause566 (q : Nat → Bool) : valuationOf q 1459 = false ∨ valuationOf q 1467 = false ∨ valuationOf q 1472 = true := by
  have hs : count1470 q = (countLit q [-3, -4, -6]) + (countLit q [-8, -11, -13, -14]) := List.countP_append (p := literal q) (l₁ := [-3, -4, -6]) (l₂ := [-8, -11, -13, -14])
  have hm := merge_two (literal (valuationOf q) (1459)) (literal (valuationOf q) (1467)) (literal (valuationOf q) (1472)) (countLit q [-3, -4, -6]) (countLit q [-8, -11, -13, -14]) (count1470 q) 1 2 (meaning1459 q) (meaning1467 q) (meaning1472 q) hs
  change valuationOf q 1459 = false ∨ valuationOf q 1467 = false ∨ valuationOf q 1472 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause566 (q : Snake 81) (h : Conditions q) : valuation q 1459 = false ∨ valuation q 1467 = false ∨ valuation q 1472 = true := counterClause566 (baseVal q)

theorem counterClause567 (q : Nat → Bool) : valuationOf q 1459 = false ∨ valuationOf q 1468 = false ∨ valuationOf q 1473 = true := by
  have hs : count1470 q = (countLit q [-3, -4, -6]) + (countLit q [-8, -11, -13, -14]) := List.countP_append (p := literal q) (l₁ := [-3, -4, -6]) (l₂ := [-8, -11, -13, -14])
  have hm := merge_two (literal (valuationOf q) (1459)) (literal (valuationOf q) (1468)) (literal (valuationOf q) (1473)) (countLit q [-3, -4, -6]) (countLit q [-8, -11, -13, -14]) (count1470 q) 1 3 (meaning1459 q) (meaning1468 q) (meaning1473 q) hs
  change valuationOf q 1459 = false ∨ valuationOf q 1468 = false ∨ valuationOf q 1473 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause567 (q : Snake 81) (h : Conditions q) : valuation q 1459 = false ∨ valuation q 1468 = false ∨ valuation q 1473 = true := counterClause567 (baseVal q)

theorem counterClause568 (q : Nat → Bool) : valuationOf q 1460 = false ∨ valuationOf q 1471 = true := by
  have hs : count1470 q = (countLit q [-3, -4, -6]) + (countLit q [-8, -11, -13, -14]) := List.countP_append (p := literal q) (l₁ := [-3, -4, -6]) (l₂ := [-8, -11, -13, -14])
  have hm := merge_left (literal (valuationOf q) (1460)) (literal (valuationOf q) (1471)) (countLit q [-3, -4, -6]) (countLit q [-8, -11, -13, -14]) (count1470 q) 2 (meaning1460 q) (meaning1471 q) hs
  change valuationOf q 1460 = false ∨ valuationOf q 1471 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause568 (q : Snake 81) (h : Conditions q) : valuation q 1460 = false ∨ valuation q 1471 = true := counterClause568 (baseVal q)

theorem counterClause569 (q : Nat → Bool) : valuationOf q 1460 = false ∨ valuationOf q 1466 = false ∨ valuationOf q 1472 = true := by
  have hs : count1470 q = (countLit q [-3, -4, -6]) + (countLit q [-8, -11, -13, -14]) := List.countP_append (p := literal q) (l₁ := [-3, -4, -6]) (l₂ := [-8, -11, -13, -14])
  have hm := merge_two (literal (valuationOf q) (1460)) (literal (valuationOf q) (1466)) (literal (valuationOf q) (1472)) (countLit q [-3, -4, -6]) (countLit q [-8, -11, -13, -14]) (count1470 q) 2 1 (meaning1460 q) (meaning1466 q) (meaning1472 q) hs
  change valuationOf q 1460 = false ∨ valuationOf q 1466 = false ∨ valuationOf q 1472 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause569 (q : Snake 81) (h : Conditions q) : valuation q 1460 = false ∨ valuation q 1466 = false ∨ valuation q 1472 = true := counterClause569 (baseVal q)

theorem counterClause570 (q : Nat → Bool) : valuationOf q 1460 = false ∨ valuationOf q 1467 = false ∨ valuationOf q 1473 = true := by
  have hs : count1470 q = (countLit q [-3, -4, -6]) + (countLit q [-8, -11, -13, -14]) := List.countP_append (p := literal q) (l₁ := [-3, -4, -6]) (l₂ := [-8, -11, -13, -14])
  have hm := merge_two (literal (valuationOf q) (1460)) (literal (valuationOf q) (1467)) (literal (valuationOf q) (1473)) (countLit q [-3, -4, -6]) (countLit q [-8, -11, -13, -14]) (count1470 q) 2 2 (meaning1460 q) (meaning1467 q) (meaning1473 q) hs
  change valuationOf q 1460 = false ∨ valuationOf q 1467 = false ∨ valuationOf q 1473 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause570 (q : Snake 81) (h : Conditions q) : valuation q 1460 = false ∨ valuation q 1467 = false ∨ valuation q 1473 = true := counterClause570 (baseVal q)

theorem counterClause571 (q : Nat → Bool) : valuationOf q 1461 = false ∨ valuationOf q 1472 = true := by
  have hs : count1470 q = (countLit q [-3, -4, -6]) + (countLit q [-8, -11, -13, -14]) := List.countP_append (p := literal q) (l₁ := [-3, -4, -6]) (l₂ := [-8, -11, -13, -14])
  have hm := merge_left (literal (valuationOf q) (1461)) (literal (valuationOf q) (1472)) (countLit q [-3, -4, -6]) (countLit q [-8, -11, -13, -14]) (count1470 q) 3 (meaning1461 q) (meaning1472 q) hs
  change valuationOf q 1461 = false ∨ valuationOf q 1472 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause571 (q : Snake 81) (h : Conditions q) : valuation q 1461 = false ∨ valuation q 1472 = true := counterClause571 (baseVal q)

theorem counterClause572 (q : Nat → Bool) : valuationOf q 1461 = false ∨ valuationOf q 1466 = false ∨ valuationOf q 1473 = true := by
  have hs : count1470 q = (countLit q [-3, -4, -6]) + (countLit q [-8, -11, -13, -14]) := List.countP_append (p := literal q) (l₁ := [-3, -4, -6]) (l₂ := [-8, -11, -13, -14])
  have hm := merge_two (literal (valuationOf q) (1461)) (literal (valuationOf q) (1466)) (literal (valuationOf q) (1473)) (countLit q [-3, -4, -6]) (countLit q [-8, -11, -13, -14]) (count1470 q) 3 1 (meaning1461 q) (meaning1466 q) (meaning1473 q) hs
  change valuationOf q 1461 = false ∨ valuationOf q 1466 = false ∨ valuationOf q 1473 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause572 (q : Snake 81) (h : Conditions q) : valuation q 1461 = false ∨ valuation q 1466 = false ∨ valuation q 1473 = true := counterClause572 (baseVal q)

theorem counterClause573 (q : Nat → Bool) : valuationOf q 21 = true ∨ valuationOf q 1477 = true := by
  have hs : count1477 q = (countLit q [-20]) + (countLit q [-21]) := List.countP_append (p := literal q) (l₁ := [-20]) (l₂ := [-21])
  have hm := merge_right (literal (valuationOf q) (-21)) (literal (valuationOf q) (1477)) (countLit q [-20]) (countLit q [-21]) (count1477 q) 1 (meaningNeg21 q) (meaning1477 q) hs
  change (! (valuationOf q 21)) = false ∨ valuationOf q 1477 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause573 (q : Snake 81) (h : Conditions q) : valuation q 21 = true ∨ valuation q 1477 = true := counterClause573 (baseVal q)

theorem counterClause574 (q : Nat → Bool) : valuationOf q 20 = true ∨ valuationOf q 1477 = true := by
  have hs : count1477 q = (countLit q [-20]) + (countLit q [-21]) := List.countP_append (p := literal q) (l₁ := [-20]) (l₂ := [-21])
  have hm := merge_left (literal (valuationOf q) (-20)) (literal (valuationOf q) (1477)) (countLit q [-20]) (countLit q [-21]) (count1477 q) 1 (meaningNeg20 q) (meaning1477 q) hs
  change (! (valuationOf q 20)) = false ∨ valuationOf q 1477 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause574 (q : Snake 81) (h : Conditions q) : valuation q 20 = true ∨ valuation q 1477 = true := counterClause574 (baseVal q)

theorem counterClause575 (q : Nat → Bool) : valuationOf q 20 = true ∨ valuationOf q 21 = true ∨ valuationOf q 1478 = true := by
  have hs : count1477 q = (countLit q [-20]) + (countLit q [-21]) := List.countP_append (p := literal q) (l₁ := [-20]) (l₂ := [-21])
  have hm := merge_two (literal (valuationOf q) (-20)) (literal (valuationOf q) (-21)) (literal (valuationOf q) (1478)) (countLit q [-20]) (countLit q [-21]) (count1477 q) 1 1 (meaningNeg20 q) (meaningNeg21 q) (meaning1478 q) hs
  change (! (valuationOf q 20)) = false ∨ (! (valuationOf q 21)) = false ∨ valuationOf q 1478 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause575 (q : Snake 81) (h : Conditions q) : valuation q 20 = true ∨ valuation q 21 = true ∨ valuation q 1478 = true := counterClause575 (baseVal q)

theorem counterClause576 (q : Nat → Bool) : valuationOf q 1477 = false ∨ valuationOf q 1479 = true := by
  have hs : count1479 q = (countLit q [-16]) + (countLit q [-20, -21]) := List.countP_append (p := literal q) (l₁ := [-16]) (l₂ := [-20, -21])
  have hm := merge_right (literal (valuationOf q) (1477)) (literal (valuationOf q) (1479)) (countLit q [-16]) (countLit q [-20, -21]) (count1479 q) 1 (meaning1477 q) (meaning1479 q) hs
  change valuationOf q 1477 = false ∨ valuationOf q 1479 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause576 (q : Snake 81) (h : Conditions q) : valuation q 1477 = false ∨ valuation q 1479 = true := counterClause576 (baseVal q)

theorem block17 (q : Snake 81) (h : Conditions q) : B112E152.Block17 (valuation q) :=
  ⟨clause545 q h, clause546 q h, clause547 q h, clause548 q h, clause549 q h, clause550 q h, clause551 q h, clause552 q h, clause553 q h, clause554 q h, clause555 q h, clause556 q h, clause557 q h, clause558 q h, clause559 q h, clause560 q h, clause561 q h, clause562 q h, clause563 q h, clause564 q h, clause565 q h, clause566 q h, clause567 q h, clause568 q h, clause569 q h, clause570 q h, clause571 q h, clause572 q h, clause573 q h, clause574 q h, clause575 q h, clause576 q h⟩

end
end Snake9.Regrowth.E112152
