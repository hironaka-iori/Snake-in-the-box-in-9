import E112168Semantics
import B112E168Inputs
namespace Snake9.Regrowth.E112168
noncomputable section
local instance blockDec27 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause865 (q : Nat → Bool) : valuationOf q 1441 = false ∨ valuationOf q 1463 = false ∨ valuationOf q 1472 = true := by
  have hs : count1467 q = (countLit q [-30, -31, -34, -36, -39, -40, -43]) + (countLit q [-44, -47, -51, -52, -54, -57, -58]) := List.countP_append (p := literal q) (l₁ := [-30, -31, -34, -36, -39, -40, -43]) (l₂ := [-44, -47, -51, -52, -54, -57, -58])
  have hm := merge_two (literal (valuationOf q) (1441)) (literal (valuationOf q) (1463)) (literal (valuationOf q) (1472)) (countLit q [-30, -31, -34, -36, -39, -40, -43]) (countLit q [-44, -47, -51, -52, -54, -57, -58]) (count1467 q) 2 4 (meaning1441 q) (meaning1463 q) (meaning1472 q) hs
  change valuationOf q 1441 = false ∨ valuationOf q 1463 = false ∨ valuationOf q 1472 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause865 (q : Snake 81) (h : Conditions q) : valuation q 1441 = false ∨ valuation q 1463 = false ∨ valuation q 1472 = true := counterClause865 (baseVal q)

theorem counterClause866 (q : Nat → Bool) : valuationOf q 1441 = false ∨ valuationOf q 1464 = false ∨ valuationOf q 1473 = true := by
  have hs : count1467 q = (countLit q [-30, -31, -34, -36, -39, -40, -43]) + (countLit q [-44, -47, -51, -52, -54, -57, -58]) := List.countP_append (p := literal q) (l₁ := [-30, -31, -34, -36, -39, -40, -43]) (l₂ := [-44, -47, -51, -52, -54, -57, -58])
  have hm := merge_two (literal (valuationOf q) (1441)) (literal (valuationOf q) (1464)) (literal (valuationOf q) (1473)) (countLit q [-30, -31, -34, -36, -39, -40, -43]) (countLit q [-44, -47, -51, -52, -54, -57, -58]) (count1467 q) 2 5 (meaning1441 q) (meaning1464 q) (meaning1473 q) hs
  change valuationOf q 1441 = false ∨ valuationOf q 1464 = false ∨ valuationOf q 1473 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause866 (q : Snake 81) (h : Conditions q) : valuation q 1441 = false ∨ valuation q 1464 = false ∨ valuation q 1473 = true := counterClause866 (baseVal q)

theorem counterClause867 (q : Nat → Bool) : valuationOf q 1441 = false ∨ valuationOf q 1465 = false ∨ valuationOf q 1474 = true := by
  have hs : count1467 q = (countLit q [-30, -31, -34, -36, -39, -40, -43]) + (countLit q [-44, -47, -51, -52, -54, -57, -58]) := List.countP_append (p := literal q) (l₁ := [-30, -31, -34, -36, -39, -40, -43]) (l₂ := [-44, -47, -51, -52, -54, -57, -58])
  have hm := merge_two (literal (valuationOf q) (1441)) (literal (valuationOf q) (1465)) (literal (valuationOf q) (1474)) (countLit q [-30, -31, -34, -36, -39, -40, -43]) (countLit q [-44, -47, -51, -52, -54, -57, -58]) (count1467 q) 2 6 (meaning1441 q) (meaning1465 q) (meaning1474 q) hs
  change valuationOf q 1441 = false ∨ valuationOf q 1465 = false ∨ valuationOf q 1474 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause867 (q : Snake 81) (h : Conditions q) : valuation q 1441 = false ∨ valuation q 1465 = false ∨ valuation q 1474 = true := counterClause867 (baseVal q)

theorem counterClause868 (q : Nat → Bool) : valuationOf q 1442 = false ∨ valuationOf q 1460 = false ∨ valuationOf q 1470 = true := by
  have hs : count1467 q = (countLit q [-30, -31, -34, -36, -39, -40, -43]) + (countLit q [-44, -47, -51, -52, -54, -57, -58]) := List.countP_append (p := literal q) (l₁ := [-30, -31, -34, -36, -39, -40, -43]) (l₂ := [-44, -47, -51, -52, -54, -57, -58])
  have hm := merge_two (literal (valuationOf q) (1442)) (literal (valuationOf q) (1460)) (literal (valuationOf q) (1470)) (countLit q [-30, -31, -34, -36, -39, -40, -43]) (countLit q [-44, -47, -51, -52, -54, -57, -58]) (count1467 q) 3 1 (meaning1442 q) (meaning1460 q) (meaning1470 q) hs
  change valuationOf q 1442 = false ∨ valuationOf q 1460 = false ∨ valuationOf q 1470 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause868 (q : Snake 81) (h : Conditions q) : valuation q 1442 = false ∨ valuation q 1460 = false ∨ valuation q 1470 = true := counterClause868 (baseVal q)

theorem counterClause869 (q : Nat → Bool) : valuationOf q 1442 = false ∨ valuationOf q 1461 = false ∨ valuationOf q 1471 = true := by
  have hs : count1467 q = (countLit q [-30, -31, -34, -36, -39, -40, -43]) + (countLit q [-44, -47, -51, -52, -54, -57, -58]) := List.countP_append (p := literal q) (l₁ := [-30, -31, -34, -36, -39, -40, -43]) (l₂ := [-44, -47, -51, -52, -54, -57, -58])
  have hm := merge_two (literal (valuationOf q) (1442)) (literal (valuationOf q) (1461)) (literal (valuationOf q) (1471)) (countLit q [-30, -31, -34, -36, -39, -40, -43]) (countLit q [-44, -47, -51, -52, -54, -57, -58]) (count1467 q) 3 2 (meaning1442 q) (meaning1461 q) (meaning1471 q) hs
  change valuationOf q 1442 = false ∨ valuationOf q 1461 = false ∨ valuationOf q 1471 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause869 (q : Snake 81) (h : Conditions q) : valuation q 1442 = false ∨ valuation q 1461 = false ∨ valuation q 1471 = true := counterClause869 (baseVal q)

theorem counterClause870 (q : Nat → Bool) : valuationOf q 1442 = false ∨ valuationOf q 1462 = false ∨ valuationOf q 1472 = true := by
  have hs : count1467 q = (countLit q [-30, -31, -34, -36, -39, -40, -43]) + (countLit q [-44, -47, -51, -52, -54, -57, -58]) := List.countP_append (p := literal q) (l₁ := [-30, -31, -34, -36, -39, -40, -43]) (l₂ := [-44, -47, -51, -52, -54, -57, -58])
  have hm := merge_two (literal (valuationOf q) (1442)) (literal (valuationOf q) (1462)) (literal (valuationOf q) (1472)) (countLit q [-30, -31, -34, -36, -39, -40, -43]) (countLit q [-44, -47, -51, -52, -54, -57, -58]) (count1467 q) 3 3 (meaning1442 q) (meaning1462 q) (meaning1472 q) hs
  change valuationOf q 1442 = false ∨ valuationOf q 1462 = false ∨ valuationOf q 1472 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause870 (q : Snake 81) (h : Conditions q) : valuation q 1442 = false ∨ valuation q 1462 = false ∨ valuation q 1472 = true := counterClause870 (baseVal q)

theorem counterClause871 (q : Nat → Bool) : valuationOf q 1442 = false ∨ valuationOf q 1463 = false ∨ valuationOf q 1473 = true := by
  have hs : count1467 q = (countLit q [-30, -31, -34, -36, -39, -40, -43]) + (countLit q [-44, -47, -51, -52, -54, -57, -58]) := List.countP_append (p := literal q) (l₁ := [-30, -31, -34, -36, -39, -40, -43]) (l₂ := [-44, -47, -51, -52, -54, -57, -58])
  have hm := merge_two (literal (valuationOf q) (1442)) (literal (valuationOf q) (1463)) (literal (valuationOf q) (1473)) (countLit q [-30, -31, -34, -36, -39, -40, -43]) (countLit q [-44, -47, -51, -52, -54, -57, -58]) (count1467 q) 3 4 (meaning1442 q) (meaning1463 q) (meaning1473 q) hs
  change valuationOf q 1442 = false ∨ valuationOf q 1463 = false ∨ valuationOf q 1473 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause871 (q : Snake 81) (h : Conditions q) : valuation q 1442 = false ∨ valuation q 1463 = false ∨ valuation q 1473 = true := counterClause871 (baseVal q)

theorem counterClause872 (q : Nat → Bool) : valuationOf q 1442 = false ∨ valuationOf q 1464 = false ∨ valuationOf q 1474 = true := by
  have hs : count1467 q = (countLit q [-30, -31, -34, -36, -39, -40, -43]) + (countLit q [-44, -47, -51, -52, -54, -57, -58]) := List.countP_append (p := literal q) (l₁ := [-30, -31, -34, -36, -39, -40, -43]) (l₂ := [-44, -47, -51, -52, -54, -57, -58])
  have hm := merge_two (literal (valuationOf q) (1442)) (literal (valuationOf q) (1464)) (literal (valuationOf q) (1474)) (countLit q [-30, -31, -34, -36, -39, -40, -43]) (countLit q [-44, -47, -51, -52, -54, -57, -58]) (count1467 q) 3 5 (meaning1442 q) (meaning1464 q) (meaning1474 q) hs
  change valuationOf q 1442 = false ∨ valuationOf q 1464 = false ∨ valuationOf q 1474 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause872 (q : Snake 81) (h : Conditions q) : valuation q 1442 = false ∨ valuation q 1464 = false ∨ valuation q 1474 = true := counterClause872 (baseVal q)

theorem counterClause873 (q : Nat → Bool) : valuationOf q 1442 = false ∨ valuationOf q 1465 = false ∨ valuationOf q 1475 = true := by
  have hs : count1467 q = (countLit q [-30, -31, -34, -36, -39, -40, -43]) + (countLit q [-44, -47, -51, -52, -54, -57, -58]) := List.countP_append (p := literal q) (l₁ := [-30, -31, -34, -36, -39, -40, -43]) (l₂ := [-44, -47, -51, -52, -54, -57, -58])
  have hm := merge_two (literal (valuationOf q) (1442)) (literal (valuationOf q) (1465)) (literal (valuationOf q) (1475)) (countLit q [-30, -31, -34, -36, -39, -40, -43]) (countLit q [-44, -47, -51, -52, -54, -57, -58]) (count1467 q) 3 6 (meaning1442 q) (meaning1465 q) (meaning1475 q) hs
  change valuationOf q 1442 = false ∨ valuationOf q 1465 = false ∨ valuationOf q 1475 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause873 (q : Snake 81) (h : Conditions q) : valuation q 1442 = false ∨ valuation q 1465 = false ∨ valuation q 1475 = true := counterClause873 (baseVal q)

theorem counterClause874 (q : Nat → Bool) : valuationOf q 1443 = false ∨ valuationOf q 1460 = false ∨ valuationOf q 1471 = true := by
  have hs : count1467 q = (countLit q [-30, -31, -34, -36, -39, -40, -43]) + (countLit q [-44, -47, -51, -52, -54, -57, -58]) := List.countP_append (p := literal q) (l₁ := [-30, -31, -34, -36, -39, -40, -43]) (l₂ := [-44, -47, -51, -52, -54, -57, -58])
  have hm := merge_two (literal (valuationOf q) (1443)) (literal (valuationOf q) (1460)) (literal (valuationOf q) (1471)) (countLit q [-30, -31, -34, -36, -39, -40, -43]) (countLit q [-44, -47, -51, -52, -54, -57, -58]) (count1467 q) 4 1 (meaning1443 q) (meaning1460 q) (meaning1471 q) hs
  change valuationOf q 1443 = false ∨ valuationOf q 1460 = false ∨ valuationOf q 1471 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause874 (q : Snake 81) (h : Conditions q) : valuation q 1443 = false ∨ valuation q 1460 = false ∨ valuation q 1471 = true := counterClause874 (baseVal q)

theorem counterClause875 (q : Nat → Bool) : valuationOf q 1443 = false ∨ valuationOf q 1461 = false ∨ valuationOf q 1472 = true := by
  have hs : count1467 q = (countLit q [-30, -31, -34, -36, -39, -40, -43]) + (countLit q [-44, -47, -51, -52, -54, -57, -58]) := List.countP_append (p := literal q) (l₁ := [-30, -31, -34, -36, -39, -40, -43]) (l₂ := [-44, -47, -51, -52, -54, -57, -58])
  have hm := merge_two (literal (valuationOf q) (1443)) (literal (valuationOf q) (1461)) (literal (valuationOf q) (1472)) (countLit q [-30, -31, -34, -36, -39, -40, -43]) (countLit q [-44, -47, -51, -52, -54, -57, -58]) (count1467 q) 4 2 (meaning1443 q) (meaning1461 q) (meaning1472 q) hs
  change valuationOf q 1443 = false ∨ valuationOf q 1461 = false ∨ valuationOf q 1472 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause875 (q : Snake 81) (h : Conditions q) : valuation q 1443 = false ∨ valuation q 1461 = false ∨ valuation q 1472 = true := counterClause875 (baseVal q)

theorem counterClause876 (q : Nat → Bool) : valuationOf q 1443 = false ∨ valuationOf q 1462 = false ∨ valuationOf q 1473 = true := by
  have hs : count1467 q = (countLit q [-30, -31, -34, -36, -39, -40, -43]) + (countLit q [-44, -47, -51, -52, -54, -57, -58]) := List.countP_append (p := literal q) (l₁ := [-30, -31, -34, -36, -39, -40, -43]) (l₂ := [-44, -47, -51, -52, -54, -57, -58])
  have hm := merge_two (literal (valuationOf q) (1443)) (literal (valuationOf q) (1462)) (literal (valuationOf q) (1473)) (countLit q [-30, -31, -34, -36, -39, -40, -43]) (countLit q [-44, -47, -51, -52, -54, -57, -58]) (count1467 q) 4 3 (meaning1443 q) (meaning1462 q) (meaning1473 q) hs
  change valuationOf q 1443 = false ∨ valuationOf q 1462 = false ∨ valuationOf q 1473 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause876 (q : Snake 81) (h : Conditions q) : valuation q 1443 = false ∨ valuation q 1462 = false ∨ valuation q 1473 = true := counterClause876 (baseVal q)

theorem counterClause877 (q : Nat → Bool) : valuationOf q 1443 = false ∨ valuationOf q 1463 = false ∨ valuationOf q 1474 = true := by
  have hs : count1467 q = (countLit q [-30, -31, -34, -36, -39, -40, -43]) + (countLit q [-44, -47, -51, -52, -54, -57, -58]) := List.countP_append (p := literal q) (l₁ := [-30, -31, -34, -36, -39, -40, -43]) (l₂ := [-44, -47, -51, -52, -54, -57, -58])
  have hm := merge_two (literal (valuationOf q) (1443)) (literal (valuationOf q) (1463)) (literal (valuationOf q) (1474)) (countLit q [-30, -31, -34, -36, -39, -40, -43]) (countLit q [-44, -47, -51, -52, -54, -57, -58]) (count1467 q) 4 4 (meaning1443 q) (meaning1463 q) (meaning1474 q) hs
  change valuationOf q 1443 = false ∨ valuationOf q 1463 = false ∨ valuationOf q 1474 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause877 (q : Snake 81) (h : Conditions q) : valuation q 1443 = false ∨ valuation q 1463 = false ∨ valuation q 1474 = true := counterClause877 (baseVal q)

theorem counterClause878 (q : Nat → Bool) : valuationOf q 1443 = false ∨ valuationOf q 1464 = false ∨ valuationOf q 1475 = true := by
  have hs : count1467 q = (countLit q [-30, -31, -34, -36, -39, -40, -43]) + (countLit q [-44, -47, -51, -52, -54, -57, -58]) := List.countP_append (p := literal q) (l₁ := [-30, -31, -34, -36, -39, -40, -43]) (l₂ := [-44, -47, -51, -52, -54, -57, -58])
  have hm := merge_two (literal (valuationOf q) (1443)) (literal (valuationOf q) (1464)) (literal (valuationOf q) (1475)) (countLit q [-30, -31, -34, -36, -39, -40, -43]) (countLit q [-44, -47, -51, -52, -54, -57, -58]) (count1467 q) 4 5 (meaning1443 q) (meaning1464 q) (meaning1475 q) hs
  change valuationOf q 1443 = false ∨ valuationOf q 1464 = false ∨ valuationOf q 1475 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause878 (q : Snake 81) (h : Conditions q) : valuation q 1443 = false ∨ valuation q 1464 = false ∨ valuation q 1475 = true := counterClause878 (baseVal q)

theorem counterClause879 (q : Nat → Bool) : valuationOf q 1413 = false ∨ valuationOf q 1474 = false ∨ valuationOf q 1489 = true := by
  have hs : count1481 q = (countLit q [-2, -3, -5, -8, -10, -11, -12, -15, -17, -18, -21, -24, -26, -29]) + (countLit q [-30, -31, -34, -36, -39, -40, -43, -44, -47, -51, -52, -54, -57, -58]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -8, -10, -11, -12, -15, -17, -18, -21, -24, -26, -29]) (l₂ := [-30, -31, -34, -36, -39, -40, -43, -44, -47, -51, -52, -54, -57, -58])
  have hm := merge_two (literal (valuationOf q) (1413)) (literal (valuationOf q) (1474)) (literal (valuationOf q) (1489)) (countLit q [-2, -3, -5, -8, -10, -11, -12, -15, -17, -18, -21, -24, -26, -29]) (countLit q [-30, -31, -34, -36, -39, -40, -43, -44, -47, -51, -52, -54, -57, -58]) (count1481 q) 1 8 (meaning1413 q) (meaning1474 q) (meaning1489 q) hs
  change valuationOf q 1413 = false ∨ valuationOf q 1474 = false ∨ valuationOf q 1489 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause879 (q : Snake 81) (h : Conditions q) : valuation q 1413 = false ∨ valuation q 1474 = false ∨ valuation q 1489 = true := counterClause879 (baseVal q)

theorem counterClause880 (q : Nat → Bool) : valuationOf q 1413 = false ∨ valuationOf q 1475 = false ∨ valuationOf q 1490 = true := by
  have hs : count1481 q = (countLit q [-2, -3, -5, -8, -10, -11, -12, -15, -17, -18, -21, -24, -26, -29]) + (countLit q [-30, -31, -34, -36, -39, -40, -43, -44, -47, -51, -52, -54, -57, -58]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -8, -10, -11, -12, -15, -17, -18, -21, -24, -26, -29]) (l₂ := [-30, -31, -34, -36, -39, -40, -43, -44, -47, -51, -52, -54, -57, -58])
  have hm := merge_two (literal (valuationOf q) (1413)) (literal (valuationOf q) (1475)) (literal (valuationOf q) (1490)) (countLit q [-2, -3, -5, -8, -10, -11, -12, -15, -17, -18, -21, -24, -26, -29]) (countLit q [-30, -31, -34, -36, -39, -40, -43, -44, -47, -51, -52, -54, -57, -58]) (count1481 q) 1 9 (meaning1413 q) (meaning1475 q) (meaning1490 q) hs
  change valuationOf q 1413 = false ∨ valuationOf q 1475 = false ∨ valuationOf q 1490 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause880 (q : Snake 81) (h : Conditions q) : valuation q 1413 = false ∨ valuation q 1475 = false ∨ valuation q 1490 = true := counterClause880 (baseVal q)

theorem counterClause881 (q : Nat → Bool) : valuationOf q 1414 = false ∨ valuationOf q 1469 = false ∨ valuationOf q 1485 = true := by
  have hs : count1481 q = (countLit q [-2, -3, -5, -8, -10, -11, -12, -15, -17, -18, -21, -24, -26, -29]) + (countLit q [-30, -31, -34, -36, -39, -40, -43, -44, -47, -51, -52, -54, -57, -58]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -8, -10, -11, -12, -15, -17, -18, -21, -24, -26, -29]) (l₂ := [-30, -31, -34, -36, -39, -40, -43, -44, -47, -51, -52, -54, -57, -58])
  have hm := merge_two (literal (valuationOf q) (1414)) (literal (valuationOf q) (1469)) (literal (valuationOf q) (1485)) (countLit q [-2, -3, -5, -8, -10, -11, -12, -15, -17, -18, -21, -24, -26, -29]) (countLit q [-30, -31, -34, -36, -39, -40, -43, -44, -47, -51, -52, -54, -57, -58]) (count1481 q) 2 3 (meaning1414 q) (meaning1469 q) (meaning1485 q) hs
  change valuationOf q 1414 = false ∨ valuationOf q 1469 = false ∨ valuationOf q 1485 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause881 (q : Snake 81) (h : Conditions q) : valuation q 1414 = false ∨ valuation q 1469 = false ∨ valuation q 1485 = true := counterClause881 (baseVal q)

theorem counterClause882 (q : Nat → Bool) : valuationOf q 1414 = false ∨ valuationOf q 1470 = false ∨ valuationOf q 1486 = true := by
  have hs : count1481 q = (countLit q [-2, -3, -5, -8, -10, -11, -12, -15, -17, -18, -21, -24, -26, -29]) + (countLit q [-30, -31, -34, -36, -39, -40, -43, -44, -47, -51, -52, -54, -57, -58]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -8, -10, -11, -12, -15, -17, -18, -21, -24, -26, -29]) (l₂ := [-30, -31, -34, -36, -39, -40, -43, -44, -47, -51, -52, -54, -57, -58])
  have hm := merge_two (literal (valuationOf q) (1414)) (literal (valuationOf q) (1470)) (literal (valuationOf q) (1486)) (countLit q [-2, -3, -5, -8, -10, -11, -12, -15, -17, -18, -21, -24, -26, -29]) (countLit q [-30, -31, -34, -36, -39, -40, -43, -44, -47, -51, -52, -54, -57, -58]) (count1481 q) 2 4 (meaning1414 q) (meaning1470 q) (meaning1486 q) hs
  change valuationOf q 1414 = false ∨ valuationOf q 1470 = false ∨ valuationOf q 1486 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause882 (q : Snake 81) (h : Conditions q) : valuation q 1414 = false ∨ valuation q 1470 = false ∨ valuation q 1486 = true := counterClause882 (baseVal q)

theorem counterClause883 (q : Nat → Bool) : valuationOf q 1414 = false ∨ valuationOf q 1471 = false ∨ valuationOf q 1487 = true := by
  have hs : count1481 q = (countLit q [-2, -3, -5, -8, -10, -11, -12, -15, -17, -18, -21, -24, -26, -29]) + (countLit q [-30, -31, -34, -36, -39, -40, -43, -44, -47, -51, -52, -54, -57, -58]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -8, -10, -11, -12, -15, -17, -18, -21, -24, -26, -29]) (l₂ := [-30, -31, -34, -36, -39, -40, -43, -44, -47, -51, -52, -54, -57, -58])
  have hm := merge_two (literal (valuationOf q) (1414)) (literal (valuationOf q) (1471)) (literal (valuationOf q) (1487)) (countLit q [-2, -3, -5, -8, -10, -11, -12, -15, -17, -18, -21, -24, -26, -29]) (countLit q [-30, -31, -34, -36, -39, -40, -43, -44, -47, -51, -52, -54, -57, -58]) (count1481 q) 2 5 (meaning1414 q) (meaning1471 q) (meaning1487 q) hs
  change valuationOf q 1414 = false ∨ valuationOf q 1471 = false ∨ valuationOf q 1487 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause883 (q : Snake 81) (h : Conditions q) : valuation q 1414 = false ∨ valuation q 1471 = false ∨ valuation q 1487 = true := counterClause883 (baseVal q)

theorem counterClause884 (q : Nat → Bool) : valuationOf q 1414 = false ∨ valuationOf q 1472 = false ∨ valuationOf q 1488 = true := by
  have hs : count1481 q = (countLit q [-2, -3, -5, -8, -10, -11, -12, -15, -17, -18, -21, -24, -26, -29]) + (countLit q [-30, -31, -34, -36, -39, -40, -43, -44, -47, -51, -52, -54, -57, -58]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -8, -10, -11, -12, -15, -17, -18, -21, -24, -26, -29]) (l₂ := [-30, -31, -34, -36, -39, -40, -43, -44, -47, -51, -52, -54, -57, -58])
  have hm := merge_two (literal (valuationOf q) (1414)) (literal (valuationOf q) (1472)) (literal (valuationOf q) (1488)) (countLit q [-2, -3, -5, -8, -10, -11, -12, -15, -17, -18, -21, -24, -26, -29]) (countLit q [-30, -31, -34, -36, -39, -40, -43, -44, -47, -51, -52, -54, -57, -58]) (count1481 q) 2 6 (meaning1414 q) (meaning1472 q) (meaning1488 q) hs
  change valuationOf q 1414 = false ∨ valuationOf q 1472 = false ∨ valuationOf q 1488 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause884 (q : Snake 81) (h : Conditions q) : valuation q 1414 = false ∨ valuation q 1472 = false ∨ valuation q 1488 = true := counterClause884 (baseVal q)

theorem counterClause885 (q : Nat → Bool) : valuationOf q 1414 = false ∨ valuationOf q 1473 = false ∨ valuationOf q 1489 = true := by
  have hs : count1481 q = (countLit q [-2, -3, -5, -8, -10, -11, -12, -15, -17, -18, -21, -24, -26, -29]) + (countLit q [-30, -31, -34, -36, -39, -40, -43, -44, -47, -51, -52, -54, -57, -58]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -8, -10, -11, -12, -15, -17, -18, -21, -24, -26, -29]) (l₂ := [-30, -31, -34, -36, -39, -40, -43, -44, -47, -51, -52, -54, -57, -58])
  have hm := merge_two (literal (valuationOf q) (1414)) (literal (valuationOf q) (1473)) (literal (valuationOf q) (1489)) (countLit q [-2, -3, -5, -8, -10, -11, -12, -15, -17, -18, -21, -24, -26, -29]) (countLit q [-30, -31, -34, -36, -39, -40, -43, -44, -47, -51, -52, -54, -57, -58]) (count1481 q) 2 7 (meaning1414 q) (meaning1473 q) (meaning1489 q) hs
  change valuationOf q 1414 = false ∨ valuationOf q 1473 = false ∨ valuationOf q 1489 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause885 (q : Snake 81) (h : Conditions q) : valuation q 1414 = false ∨ valuation q 1473 = false ∨ valuation q 1489 = true := counterClause885 (baseVal q)

theorem counterClause886 (q : Nat → Bool) : valuationOf q 1414 = false ∨ valuationOf q 1474 = false ∨ valuationOf q 1490 = true := by
  have hs : count1481 q = (countLit q [-2, -3, -5, -8, -10, -11, -12, -15, -17, -18, -21, -24, -26, -29]) + (countLit q [-30, -31, -34, -36, -39, -40, -43, -44, -47, -51, -52, -54, -57, -58]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -8, -10, -11, -12, -15, -17, -18, -21, -24, -26, -29]) (l₂ := [-30, -31, -34, -36, -39, -40, -43, -44, -47, -51, -52, -54, -57, -58])
  have hm := merge_two (literal (valuationOf q) (1414)) (literal (valuationOf q) (1474)) (literal (valuationOf q) (1490)) (countLit q [-2, -3, -5, -8, -10, -11, -12, -15, -17, -18, -21, -24, -26, -29]) (countLit q [-30, -31, -34, -36, -39, -40, -43, -44, -47, -51, -52, -54, -57, -58]) (count1481 q) 2 8 (meaning1414 q) (meaning1474 q) (meaning1490 q) hs
  change valuationOf q 1414 = false ∨ valuationOf q 1474 = false ∨ valuationOf q 1490 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause886 (q : Snake 81) (h : Conditions q) : valuation q 1414 = false ∨ valuation q 1474 = false ∨ valuation q 1490 = true := counterClause886 (baseVal q)

theorem counterClause887 (q : Nat → Bool) : valuationOf q 1414 = false ∨ valuationOf q 1475 = false ∨ valuationOf q 1491 = true := by
  have hs : count1481 q = (countLit q [-2, -3, -5, -8, -10, -11, -12, -15, -17, -18, -21, -24, -26, -29]) + (countLit q [-30, -31, -34, -36, -39, -40, -43, -44, -47, -51, -52, -54, -57, -58]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -8, -10, -11, -12, -15, -17, -18, -21, -24, -26, -29]) (l₂ := [-30, -31, -34, -36, -39, -40, -43, -44, -47, -51, -52, -54, -57, -58])
  have hm := merge_two (literal (valuationOf q) (1414)) (literal (valuationOf q) (1475)) (literal (valuationOf q) (1491)) (countLit q [-2, -3, -5, -8, -10, -11, -12, -15, -17, -18, -21, -24, -26, -29]) (countLit q [-30, -31, -34, -36, -39, -40, -43, -44, -47, -51, -52, -54, -57, -58]) (count1481 q) 2 9 (meaning1414 q) (meaning1475 q) (meaning1491 q) hs
  change valuationOf q 1414 = false ∨ valuationOf q 1475 = false ∨ valuationOf q 1491 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause887 (q : Snake 81) (h : Conditions q) : valuation q 1414 = false ∨ valuation q 1475 = false ∨ valuation q 1491 = true := counterClause887 (baseVal q)

theorem counterClause888 (q : Nat → Bool) : valuationOf q 1415 = false ∨ valuationOf q 1468 = false ∨ valuationOf q 1485 = true := by
  have hs : count1481 q = (countLit q [-2, -3, -5, -8, -10, -11, -12, -15, -17, -18, -21, -24, -26, -29]) + (countLit q [-30, -31, -34, -36, -39, -40, -43, -44, -47, -51, -52, -54, -57, -58]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -8, -10, -11, -12, -15, -17, -18, -21, -24, -26, -29]) (l₂ := [-30, -31, -34, -36, -39, -40, -43, -44, -47, -51, -52, -54, -57, -58])
  have hm := merge_two (literal (valuationOf q) (1415)) (literal (valuationOf q) (1468)) (literal (valuationOf q) (1485)) (countLit q [-2, -3, -5, -8, -10, -11, -12, -15, -17, -18, -21, -24, -26, -29]) (countLit q [-30, -31, -34, -36, -39, -40, -43, -44, -47, -51, -52, -54, -57, -58]) (count1481 q) 3 2 (meaning1415 q) (meaning1468 q) (meaning1485 q) hs
  change valuationOf q 1415 = false ∨ valuationOf q 1468 = false ∨ valuationOf q 1485 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause888 (q : Snake 81) (h : Conditions q) : valuation q 1415 = false ∨ valuation q 1468 = false ∨ valuation q 1485 = true := counterClause888 (baseVal q)

theorem counterClause889 (q : Nat → Bool) : valuationOf q 1415 = false ∨ valuationOf q 1469 = false ∨ valuationOf q 1486 = true := by
  have hs : count1481 q = (countLit q [-2, -3, -5, -8, -10, -11, -12, -15, -17, -18, -21, -24, -26, -29]) + (countLit q [-30, -31, -34, -36, -39, -40, -43, -44, -47, -51, -52, -54, -57, -58]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -8, -10, -11, -12, -15, -17, -18, -21, -24, -26, -29]) (l₂ := [-30, -31, -34, -36, -39, -40, -43, -44, -47, -51, -52, -54, -57, -58])
  have hm := merge_two (literal (valuationOf q) (1415)) (literal (valuationOf q) (1469)) (literal (valuationOf q) (1486)) (countLit q [-2, -3, -5, -8, -10, -11, -12, -15, -17, -18, -21, -24, -26, -29]) (countLit q [-30, -31, -34, -36, -39, -40, -43, -44, -47, -51, -52, -54, -57, -58]) (count1481 q) 3 3 (meaning1415 q) (meaning1469 q) (meaning1486 q) hs
  change valuationOf q 1415 = false ∨ valuationOf q 1469 = false ∨ valuationOf q 1486 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause889 (q : Snake 81) (h : Conditions q) : valuation q 1415 = false ∨ valuation q 1469 = false ∨ valuation q 1486 = true := counterClause889 (baseVal q)

theorem counterClause890 (q : Nat → Bool) : valuationOf q 1415 = false ∨ valuationOf q 1470 = false ∨ valuationOf q 1487 = true := by
  have hs : count1481 q = (countLit q [-2, -3, -5, -8, -10, -11, -12, -15, -17, -18, -21, -24, -26, -29]) + (countLit q [-30, -31, -34, -36, -39, -40, -43, -44, -47, -51, -52, -54, -57, -58]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -8, -10, -11, -12, -15, -17, -18, -21, -24, -26, -29]) (l₂ := [-30, -31, -34, -36, -39, -40, -43, -44, -47, -51, -52, -54, -57, -58])
  have hm := merge_two (literal (valuationOf q) (1415)) (literal (valuationOf q) (1470)) (literal (valuationOf q) (1487)) (countLit q [-2, -3, -5, -8, -10, -11, -12, -15, -17, -18, -21, -24, -26, -29]) (countLit q [-30, -31, -34, -36, -39, -40, -43, -44, -47, -51, -52, -54, -57, -58]) (count1481 q) 3 4 (meaning1415 q) (meaning1470 q) (meaning1487 q) hs
  change valuationOf q 1415 = false ∨ valuationOf q 1470 = false ∨ valuationOf q 1487 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause890 (q : Snake 81) (h : Conditions q) : valuation q 1415 = false ∨ valuation q 1470 = false ∨ valuation q 1487 = true := counterClause890 (baseVal q)

theorem counterClause891 (q : Nat → Bool) : valuationOf q 1415 = false ∨ valuationOf q 1471 = false ∨ valuationOf q 1488 = true := by
  have hs : count1481 q = (countLit q [-2, -3, -5, -8, -10, -11, -12, -15, -17, -18, -21, -24, -26, -29]) + (countLit q [-30, -31, -34, -36, -39, -40, -43, -44, -47, -51, -52, -54, -57, -58]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -8, -10, -11, -12, -15, -17, -18, -21, -24, -26, -29]) (l₂ := [-30, -31, -34, -36, -39, -40, -43, -44, -47, -51, -52, -54, -57, -58])
  have hm := merge_two (literal (valuationOf q) (1415)) (literal (valuationOf q) (1471)) (literal (valuationOf q) (1488)) (countLit q [-2, -3, -5, -8, -10, -11, -12, -15, -17, -18, -21, -24, -26, -29]) (countLit q [-30, -31, -34, -36, -39, -40, -43, -44, -47, -51, -52, -54, -57, -58]) (count1481 q) 3 5 (meaning1415 q) (meaning1471 q) (meaning1488 q) hs
  change valuationOf q 1415 = false ∨ valuationOf q 1471 = false ∨ valuationOf q 1488 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause891 (q : Snake 81) (h : Conditions q) : valuation q 1415 = false ∨ valuation q 1471 = false ∨ valuation q 1488 = true := counterClause891 (baseVal q)

theorem counterClause892 (q : Nat → Bool) : valuationOf q 1415 = false ∨ valuationOf q 1472 = false ∨ valuationOf q 1489 = true := by
  have hs : count1481 q = (countLit q [-2, -3, -5, -8, -10, -11, -12, -15, -17, -18, -21, -24, -26, -29]) + (countLit q [-30, -31, -34, -36, -39, -40, -43, -44, -47, -51, -52, -54, -57, -58]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -8, -10, -11, -12, -15, -17, -18, -21, -24, -26, -29]) (l₂ := [-30, -31, -34, -36, -39, -40, -43, -44, -47, -51, -52, -54, -57, -58])
  have hm := merge_two (literal (valuationOf q) (1415)) (literal (valuationOf q) (1472)) (literal (valuationOf q) (1489)) (countLit q [-2, -3, -5, -8, -10, -11, -12, -15, -17, -18, -21, -24, -26, -29]) (countLit q [-30, -31, -34, -36, -39, -40, -43, -44, -47, -51, -52, -54, -57, -58]) (count1481 q) 3 6 (meaning1415 q) (meaning1472 q) (meaning1489 q) hs
  change valuationOf q 1415 = false ∨ valuationOf q 1472 = false ∨ valuationOf q 1489 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause892 (q : Snake 81) (h : Conditions q) : valuation q 1415 = false ∨ valuation q 1472 = false ∨ valuation q 1489 = true := counterClause892 (baseVal q)

theorem counterClause893 (q : Nat → Bool) : valuationOf q 1415 = false ∨ valuationOf q 1473 = false ∨ valuationOf q 1490 = true := by
  have hs : count1481 q = (countLit q [-2, -3, -5, -8, -10, -11, -12, -15, -17, -18, -21, -24, -26, -29]) + (countLit q [-30, -31, -34, -36, -39, -40, -43, -44, -47, -51, -52, -54, -57, -58]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -8, -10, -11, -12, -15, -17, -18, -21, -24, -26, -29]) (l₂ := [-30, -31, -34, -36, -39, -40, -43, -44, -47, -51, -52, -54, -57, -58])
  have hm := merge_two (literal (valuationOf q) (1415)) (literal (valuationOf q) (1473)) (literal (valuationOf q) (1490)) (countLit q [-2, -3, -5, -8, -10, -11, -12, -15, -17, -18, -21, -24, -26, -29]) (countLit q [-30, -31, -34, -36, -39, -40, -43, -44, -47, -51, -52, -54, -57, -58]) (count1481 q) 3 7 (meaning1415 q) (meaning1473 q) (meaning1490 q) hs
  change valuationOf q 1415 = false ∨ valuationOf q 1473 = false ∨ valuationOf q 1490 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause893 (q : Snake 81) (h : Conditions q) : valuation q 1415 = false ∨ valuation q 1473 = false ∨ valuation q 1490 = true := counterClause893 (baseVal q)

theorem counterClause894 (q : Nat → Bool) : valuationOf q 1415 = false ∨ valuationOf q 1474 = false ∨ valuationOf q 1491 = true := by
  have hs : count1481 q = (countLit q [-2, -3, -5, -8, -10, -11, -12, -15, -17, -18, -21, -24, -26, -29]) + (countLit q [-30, -31, -34, -36, -39, -40, -43, -44, -47, -51, -52, -54, -57, -58]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -8, -10, -11, -12, -15, -17, -18, -21, -24, -26, -29]) (l₂ := [-30, -31, -34, -36, -39, -40, -43, -44, -47, -51, -52, -54, -57, -58])
  have hm := merge_two (literal (valuationOf q) (1415)) (literal (valuationOf q) (1474)) (literal (valuationOf q) (1491)) (countLit q [-2, -3, -5, -8, -10, -11, -12, -15, -17, -18, -21, -24, -26, -29]) (countLit q [-30, -31, -34, -36, -39, -40, -43, -44, -47, -51, -52, -54, -57, -58]) (count1481 q) 3 8 (meaning1415 q) (meaning1474 q) (meaning1491 q) hs
  change valuationOf q 1415 = false ∨ valuationOf q 1474 = false ∨ valuationOf q 1491 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause894 (q : Snake 81) (h : Conditions q) : valuation q 1415 = false ∨ valuation q 1474 = false ∨ valuation q 1491 = true := counterClause894 (baseVal q)

theorem counterClause895 (q : Nat → Bool) : valuationOf q 1415 = false ∨ valuationOf q 1475 = false ∨ valuationOf q 1492 = true := by
  have hs : count1481 q = (countLit q [-2, -3, -5, -8, -10, -11, -12, -15, -17, -18, -21, -24, -26, -29]) + (countLit q [-30, -31, -34, -36, -39, -40, -43, -44, -47, -51, -52, -54, -57, -58]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -8, -10, -11, -12, -15, -17, -18, -21, -24, -26, -29]) (l₂ := [-30, -31, -34, -36, -39, -40, -43, -44, -47, -51, -52, -54, -57, -58])
  have hm := merge_two (literal (valuationOf q) (1415)) (literal (valuationOf q) (1475)) (literal (valuationOf q) (1492)) (countLit q [-2, -3, -5, -8, -10, -11, -12, -15, -17, -18, -21, -24, -26, -29]) (countLit q [-30, -31, -34, -36, -39, -40, -43, -44, -47, -51, -52, -54, -57, -58]) (count1481 q) 3 9 (meaning1415 q) (meaning1475 q) (meaning1492 q) hs
  change valuationOf q 1415 = false ∨ valuationOf q 1475 = false ∨ valuationOf q 1492 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause895 (q : Snake 81) (h : Conditions q) : valuation q 1415 = false ∨ valuation q 1475 = false ∨ valuation q 1492 = true := counterClause895 (baseVal q)

theorem counterClause896 (q : Nat → Bool) : valuationOf q 1416 = false ∨ valuationOf q 1468 = false ∨ valuationOf q 1486 = true := by
  have hs : count1481 q = (countLit q [-2, -3, -5, -8, -10, -11, -12, -15, -17, -18, -21, -24, -26, -29]) + (countLit q [-30, -31, -34, -36, -39, -40, -43, -44, -47, -51, -52, -54, -57, -58]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -8, -10, -11, -12, -15, -17, -18, -21, -24, -26, -29]) (l₂ := [-30, -31, -34, -36, -39, -40, -43, -44, -47, -51, -52, -54, -57, -58])
  have hm := merge_two (literal (valuationOf q) (1416)) (literal (valuationOf q) (1468)) (literal (valuationOf q) (1486)) (countLit q [-2, -3, -5, -8, -10, -11, -12, -15, -17, -18, -21, -24, -26, -29]) (countLit q [-30, -31, -34, -36, -39, -40, -43, -44, -47, -51, -52, -54, -57, -58]) (count1481 q) 4 2 (meaning1416 q) (meaning1468 q) (meaning1486 q) hs
  change valuationOf q 1416 = false ∨ valuationOf q 1468 = false ∨ valuationOf q 1486 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause896 (q : Snake 81) (h : Conditions q) : valuation q 1416 = false ∨ valuation q 1468 = false ∨ valuation q 1486 = true := counterClause896 (baseVal q)

theorem block27 (q : Snake 81) (h : Conditions q) : B112E168.Block27 (valuation q) :=
  ⟨clause865 q h, clause866 q h, clause867 q h, clause868 q h, clause869 q h, clause870 q h, clause871 q h, clause872 q h, clause873 q h, clause874 q h, clause875 q h, clause876 q h, clause877 q h, clause878 q h, clause879 q h, clause880 q h, clause881 q h, clause882 q h, clause883 q h, clause884 q h, clause885 q h, clause886 q h, clause887 q h, clause888 q h, clause889 q h, clause890 q h, clause891 q h, clause892 q h, clause893 q h, clause894 q h, clause895 q h, clause896 q h⟩

end
end Snake9.Regrowth.E112168
