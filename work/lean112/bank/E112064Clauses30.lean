import E112064Semantics
import B112E064Inputs
namespace Snake9.Regrowth.E112064
noncomputable section
local instance blockDec30 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause961 (q : Nat → Bool) : valuationOf q 1435 = false ∨ valuationOf q 1439 = true := by
  have hs : count1436 q = (countLit q [-16, -19, -20]) + (countLit q [-22, -24, -25, -26]) := List.countP_append (p := literal q) (l₁ := [-16, -19, -20]) (l₂ := [-22, -24, -25, -26])
  have hm := merge_right (literal (valuationOf q) (1435)) (literal (valuationOf q) (1439)) (countLit q [-16, -19, -20]) (countLit q [-22, -24, -25, -26]) (count1436 q) 4 (meaning1435 q) (meaning1439 q) hs
  change valuationOf q 1435 = false ∨ valuationOf q 1439 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause961 (q : Snake 81) (h : Conditions q) : valuation q 1435 = false ∨ valuation q 1439 = true := counterClause961 (baseVal q)

theorem counterClause962 (q : Nat → Bool) : valuationOf q 1425 = false ∨ valuationOf q 1433 = false ∨ valuationOf q 1438 = true := by
  have hs : count1436 q = (countLit q [-16, -19, -20]) + (countLit q [-22, -24, -25, -26]) := List.countP_append (p := literal q) (l₁ := [-16, -19, -20]) (l₂ := [-22, -24, -25, -26])
  have hm := merge_two (literal (valuationOf q) (1425)) (literal (valuationOf q) (1433)) (literal (valuationOf q) (1438)) (countLit q [-16, -19, -20]) (countLit q [-22, -24, -25, -26]) (count1436 q) 1 2 (meaning1425 q) (meaning1433 q) (meaning1438 q) hs
  change valuationOf q 1425 = false ∨ valuationOf q 1433 = false ∨ valuationOf q 1438 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause962 (q : Snake 81) (h : Conditions q) : valuation q 1425 = false ∨ valuation q 1433 = false ∨ valuation q 1438 = true := counterClause962 (baseVal q)

theorem counterClause963 (q : Nat → Bool) : valuationOf q 1425 = false ∨ valuationOf q 1434 = false ∨ valuationOf q 1439 = true := by
  have hs : count1436 q = (countLit q [-16, -19, -20]) + (countLit q [-22, -24, -25, -26]) := List.countP_append (p := literal q) (l₁ := [-16, -19, -20]) (l₂ := [-22, -24, -25, -26])
  have hm := merge_two (literal (valuationOf q) (1425)) (literal (valuationOf q) (1434)) (literal (valuationOf q) (1439)) (countLit q [-16, -19, -20]) (countLit q [-22, -24, -25, -26]) (count1436 q) 1 3 (meaning1425 q) (meaning1434 q) (meaning1439 q) hs
  change valuationOf q 1425 = false ∨ valuationOf q 1434 = false ∨ valuationOf q 1439 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause963 (q : Snake 81) (h : Conditions q) : valuation q 1425 = false ∨ valuation q 1434 = false ∨ valuation q 1439 = true := counterClause963 (baseVal q)

theorem counterClause964 (q : Nat → Bool) : valuationOf q 1425 = false ∨ valuationOf q 1435 = false ∨ valuationOf q 1440 = true := by
  have hs : count1436 q = (countLit q [-16, -19, -20]) + (countLit q [-22, -24, -25, -26]) := List.countP_append (p := literal q) (l₁ := [-16, -19, -20]) (l₂ := [-22, -24, -25, -26])
  have hm := merge_two (literal (valuationOf q) (1425)) (literal (valuationOf q) (1435)) (literal (valuationOf q) (1440)) (countLit q [-16, -19, -20]) (countLit q [-22, -24, -25, -26]) (count1436 q) 1 4 (meaning1425 q) (meaning1435 q) (meaning1440 q) hs
  change valuationOf q 1425 = false ∨ valuationOf q 1435 = false ∨ valuationOf q 1440 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause964 (q : Snake 81) (h : Conditions q) : valuation q 1425 = false ∨ valuation q 1435 = false ∨ valuation q 1440 = true := counterClause964 (baseVal q)

theorem counterClause965 (q : Nat → Bool) : valuationOf q 1426 = false ∨ valuationOf q 1433 = false ∨ valuationOf q 1439 = true := by
  have hs : count1436 q = (countLit q [-16, -19, -20]) + (countLit q [-22, -24, -25, -26]) := List.countP_append (p := literal q) (l₁ := [-16, -19, -20]) (l₂ := [-22, -24, -25, -26])
  have hm := merge_two (literal (valuationOf q) (1426)) (literal (valuationOf q) (1433)) (literal (valuationOf q) (1439)) (countLit q [-16, -19, -20]) (countLit q [-22, -24, -25, -26]) (count1436 q) 2 2 (meaning1426 q) (meaning1433 q) (meaning1439 q) hs
  change valuationOf q 1426 = false ∨ valuationOf q 1433 = false ∨ valuationOf q 1439 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause965 (q : Snake 81) (h : Conditions q) : valuation q 1426 = false ∨ valuation q 1433 = false ∨ valuation q 1439 = true := counterClause965 (baseVal q)

theorem counterClause966 (q : Nat → Bool) : valuationOf q 1426 = false ∨ valuationOf q 1434 = false ∨ valuationOf q 1440 = true := by
  have hs : count1436 q = (countLit q [-16, -19, -20]) + (countLit q [-22, -24, -25, -26]) := List.countP_append (p := literal q) (l₁ := [-16, -19, -20]) (l₂ := [-22, -24, -25, -26])
  have hm := merge_two (literal (valuationOf q) (1426)) (literal (valuationOf q) (1434)) (literal (valuationOf q) (1440)) (countLit q [-16, -19, -20]) (countLit q [-22, -24, -25, -26]) (count1436 q) 2 3 (meaning1426 q) (meaning1434 q) (meaning1440 q) hs
  change valuationOf q 1426 = false ∨ valuationOf q 1434 = false ∨ valuationOf q 1440 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause966 (q : Snake 81) (h : Conditions q) : valuation q 1426 = false ∨ valuation q 1434 = false ∨ valuation q 1440 = true := counterClause966 (baseVal q)

theorem counterClause967 (q : Nat → Bool) : valuationOf q 1426 = false ∨ valuationOf q 1435 = false ∨ valuationOf q 1441 = true := by
  have hs : count1436 q = (countLit q [-16, -19, -20]) + (countLit q [-22, -24, -25, -26]) := List.countP_append (p := literal q) (l₁ := [-16, -19, -20]) (l₂ := [-22, -24, -25, -26])
  have hm := merge_two (literal (valuationOf q) (1426)) (literal (valuationOf q) (1435)) (literal (valuationOf q) (1441)) (countLit q [-16, -19, -20]) (countLit q [-22, -24, -25, -26]) (count1436 q) 2 4 (meaning1426 q) (meaning1435 q) (meaning1441 q) hs
  change valuationOf q 1426 = false ∨ valuationOf q 1435 = false ∨ valuationOf q 1441 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause967 (q : Snake 81) (h : Conditions q) : valuation q 1426 = false ∨ valuation q 1435 = false ∨ valuation q 1441 = true := counterClause967 (baseVal q)

theorem counterClause968 (q : Nat → Bool) : valuationOf q 1427 = false ∨ valuationOf q 1433 = false ∨ valuationOf q 1440 = true := by
  have hs : count1436 q = (countLit q [-16, -19, -20]) + (countLit q [-22, -24, -25, -26]) := List.countP_append (p := literal q) (l₁ := [-16, -19, -20]) (l₂ := [-22, -24, -25, -26])
  have hm := merge_two (literal (valuationOf q) (1427)) (literal (valuationOf q) (1433)) (literal (valuationOf q) (1440)) (countLit q [-16, -19, -20]) (countLit q [-22, -24, -25, -26]) (count1436 q) 3 2 (meaning1427 q) (meaning1433 q) (meaning1440 q) hs
  change valuationOf q 1427 = false ∨ valuationOf q 1433 = false ∨ valuationOf q 1440 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause968 (q : Snake 81) (h : Conditions q) : valuation q 1427 = false ∨ valuation q 1433 = false ∨ valuation q 1440 = true := counterClause968 (baseVal q)

theorem counterClause969 (q : Nat → Bool) : valuationOf q 1427 = false ∨ valuationOf q 1434 = false ∨ valuationOf q 1441 = true := by
  have hs : count1436 q = (countLit q [-16, -19, -20]) + (countLit q [-22, -24, -25, -26]) := List.countP_append (p := literal q) (l₁ := [-16, -19, -20]) (l₂ := [-22, -24, -25, -26])
  have hm := merge_two (literal (valuationOf q) (1427)) (literal (valuationOf q) (1434)) (literal (valuationOf q) (1441)) (countLit q [-16, -19, -20]) (countLit q [-22, -24, -25, -26]) (count1436 q) 3 3 (meaning1427 q) (meaning1434 q) (meaning1441 q) hs
  change valuationOf q 1427 = false ∨ valuationOf q 1434 = false ∨ valuationOf q 1441 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause969 (q : Snake 81) (h : Conditions q) : valuation q 1427 = false ∨ valuation q 1434 = false ∨ valuation q 1441 = true := counterClause969 (baseVal q)

theorem counterClause970 (q : Nat → Bool) : valuationOf q 1427 = false ∨ valuationOf q 1435 = false ∨ valuationOf q 1442 = true := by
  have hs : count1436 q = (countLit q [-16, -19, -20]) + (countLit q [-22, -24, -25, -26]) := List.countP_append (p := literal q) (l₁ := [-16, -19, -20]) (l₂ := [-22, -24, -25, -26])
  have hm := merge_two (literal (valuationOf q) (1427)) (literal (valuationOf q) (1435)) (literal (valuationOf q) (1442)) (countLit q [-16, -19, -20]) (countLit q [-22, -24, -25, -26]) (count1436 q) 3 4 (meaning1427 q) (meaning1435 q) (meaning1442 q) hs
  change valuationOf q 1427 = false ∨ valuationOf q 1435 = false ∨ valuationOf q 1442 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause970 (q : Snake 81) (h : Conditions q) : valuation q 1427 = false ∨ valuation q 1435 = false ∨ valuation q 1442 = true := counterClause970 (baseVal q)

theorem counterClause971 (q : Nat → Bool) : valuationOf q 1416 = false ∨ valuationOf q 1437 = false ∨ valuationOf q 1445 = true := by
  have hs : count1443 q = (countLit q [-2, -3, -5, -6, -12, -13, -15]) + (countLit q [-16, -19, -20, -22, -24, -25, -26]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -6, -12, -13, -15]) (l₂ := [-16, -19, -20, -22, -24, -25, -26])
  have hm := merge_two (literal (valuationOf q) (1416)) (literal (valuationOf q) (1437)) (literal (valuationOf q) (1445)) (countLit q [-2, -3, -5, -6, -12, -13, -15]) (countLit q [-16, -19, -20, -22, -24, -25, -26]) (count1443 q) 1 2 (meaning1416 q) (meaning1437 q) (meaning1445 q) hs
  change valuationOf q 1416 = false ∨ valuationOf q 1437 = false ∨ valuationOf q 1445 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause971 (q : Snake 81) (h : Conditions q) : valuation q 1416 = false ∨ valuation q 1437 = false ∨ valuation q 1445 = true := counterClause971 (baseVal q)

theorem counterClause972 (q : Nat → Bool) : valuationOf q 1416 = false ∨ valuationOf q 1438 = false ∨ valuationOf q 1446 = true := by
  have hs : count1443 q = (countLit q [-2, -3, -5, -6, -12, -13, -15]) + (countLit q [-16, -19, -20, -22, -24, -25, -26]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -6, -12, -13, -15]) (l₂ := [-16, -19, -20, -22, -24, -25, -26])
  have hm := merge_two (literal (valuationOf q) (1416)) (literal (valuationOf q) (1438)) (literal (valuationOf q) (1446)) (countLit q [-2, -3, -5, -6, -12, -13, -15]) (countLit q [-16, -19, -20, -22, -24, -25, -26]) (count1443 q) 1 3 (meaning1416 q) (meaning1438 q) (meaning1446 q) hs
  change valuationOf q 1416 = false ∨ valuationOf q 1438 = false ∨ valuationOf q 1446 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause972 (q : Snake 81) (h : Conditions q) : valuation q 1416 = false ∨ valuation q 1438 = false ∨ valuation q 1446 = true := counterClause972 (baseVal q)

theorem counterClause973 (q : Nat → Bool) : valuationOf q 1416 = false ∨ valuationOf q 1439 = false ∨ valuationOf q 1447 = true := by
  have hs : count1443 q = (countLit q [-2, -3, -5, -6, -12, -13, -15]) + (countLit q [-16, -19, -20, -22, -24, -25, -26]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -6, -12, -13, -15]) (l₂ := [-16, -19, -20, -22, -24, -25, -26])
  have hm := merge_two (literal (valuationOf q) (1416)) (literal (valuationOf q) (1439)) (literal (valuationOf q) (1447)) (countLit q [-2, -3, -5, -6, -12, -13, -15]) (countLit q [-16, -19, -20, -22, -24, -25, -26]) (count1443 q) 1 4 (meaning1416 q) (meaning1439 q) (meaning1447 q) hs
  change valuationOf q 1416 = false ∨ valuationOf q 1439 = false ∨ valuationOf q 1447 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause973 (q : Snake 81) (h : Conditions q) : valuation q 1416 = false ∨ valuation q 1439 = false ∨ valuation q 1447 = true := counterClause973 (baseVal q)

theorem counterClause974 (q : Nat → Bool) : valuationOf q 1416 = false ∨ valuationOf q 1440 = false ∨ valuationOf q 1448 = true := by
  have hs : count1443 q = (countLit q [-2, -3, -5, -6, -12, -13, -15]) + (countLit q [-16, -19, -20, -22, -24, -25, -26]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -6, -12, -13, -15]) (l₂ := [-16, -19, -20, -22, -24, -25, -26])
  have hm := merge_two (literal (valuationOf q) (1416)) (literal (valuationOf q) (1440)) (literal (valuationOf q) (1448)) (countLit q [-2, -3, -5, -6, -12, -13, -15]) (countLit q [-16, -19, -20, -22, -24, -25, -26]) (count1443 q) 1 5 (meaning1416 q) (meaning1440 q) (meaning1448 q) hs
  change valuationOf q 1416 = false ∨ valuationOf q 1440 = false ∨ valuationOf q 1448 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause974 (q : Snake 81) (h : Conditions q) : valuation q 1416 = false ∨ valuation q 1440 = false ∨ valuation q 1448 = true := counterClause974 (baseVal q)

theorem counterClause975 (q : Nat → Bool) : valuationOf q 1416 = false ∨ valuationOf q 1441 = false ∨ valuationOf q 1449 = true := by
  have hs : count1443 q = (countLit q [-2, -3, -5, -6, -12, -13, -15]) + (countLit q [-16, -19, -20, -22, -24, -25, -26]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -6, -12, -13, -15]) (l₂ := [-16, -19, -20, -22, -24, -25, -26])
  have hm := merge_two (literal (valuationOf q) (1416)) (literal (valuationOf q) (1441)) (literal (valuationOf q) (1449)) (countLit q [-2, -3, -5, -6, -12, -13, -15]) (countLit q [-16, -19, -20, -22, -24, -25, -26]) (count1443 q) 1 6 (meaning1416 q) (meaning1441 q) (meaning1449 q) hs
  change valuationOf q 1416 = false ∨ valuationOf q 1441 = false ∨ valuationOf q 1449 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause975 (q : Snake 81) (h : Conditions q) : valuation q 1416 = false ∨ valuation q 1441 = false ∨ valuation q 1449 = true := counterClause975 (baseVal q)

theorem counterClause976 (q : Nat → Bool) : valuationOf q 1416 = false ∨ valuationOf q 1442 = false ∨ valuationOf q 1450 = true := by
  have hs : count1443 q = (countLit q [-2, -3, -5, -6, -12, -13, -15]) + (countLit q [-16, -19, -20, -22, -24, -25, -26]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -6, -12, -13, -15]) (l₂ := [-16, -19, -20, -22, -24, -25, -26])
  have hm := merge_two (literal (valuationOf q) (1416)) (literal (valuationOf q) (1442)) (literal (valuationOf q) (1450)) (countLit q [-2, -3, -5, -6, -12, -13, -15]) (countLit q [-16, -19, -20, -22, -24, -25, -26]) (count1443 q) 1 7 (meaning1416 q) (meaning1442 q) (meaning1450 q) hs
  change valuationOf q 1416 = false ∨ valuationOf q 1442 = false ∨ valuationOf q 1450 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause976 (q : Snake 81) (h : Conditions q) : valuation q 1416 = false ∨ valuation q 1442 = false ∨ valuation q 1450 = true := counterClause976 (baseVal q)

theorem counterClause977 (q : Nat → Bool) : valuationOf q 1417 = false ∨ valuationOf q 1437 = false ∨ valuationOf q 1446 = true := by
  have hs : count1443 q = (countLit q [-2, -3, -5, -6, -12, -13, -15]) + (countLit q [-16, -19, -20, -22, -24, -25, -26]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -6, -12, -13, -15]) (l₂ := [-16, -19, -20, -22, -24, -25, -26])
  have hm := merge_two (literal (valuationOf q) (1417)) (literal (valuationOf q) (1437)) (literal (valuationOf q) (1446)) (countLit q [-2, -3, -5, -6, -12, -13, -15]) (countLit q [-16, -19, -20, -22, -24, -25, -26]) (count1443 q) 2 2 (meaning1417 q) (meaning1437 q) (meaning1446 q) hs
  change valuationOf q 1417 = false ∨ valuationOf q 1437 = false ∨ valuationOf q 1446 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause977 (q : Snake 81) (h : Conditions q) : valuation q 1417 = false ∨ valuation q 1437 = false ∨ valuation q 1446 = true := counterClause977 (baseVal q)

theorem counterClause978 (q : Nat → Bool) : valuationOf q 1417 = false ∨ valuationOf q 1438 = false ∨ valuationOf q 1447 = true := by
  have hs : count1443 q = (countLit q [-2, -3, -5, -6, -12, -13, -15]) + (countLit q [-16, -19, -20, -22, -24, -25, -26]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -6, -12, -13, -15]) (l₂ := [-16, -19, -20, -22, -24, -25, -26])
  have hm := merge_two (literal (valuationOf q) (1417)) (literal (valuationOf q) (1438)) (literal (valuationOf q) (1447)) (countLit q [-2, -3, -5, -6, -12, -13, -15]) (countLit q [-16, -19, -20, -22, -24, -25, -26]) (count1443 q) 2 3 (meaning1417 q) (meaning1438 q) (meaning1447 q) hs
  change valuationOf q 1417 = false ∨ valuationOf q 1438 = false ∨ valuationOf q 1447 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause978 (q : Snake 81) (h : Conditions q) : valuation q 1417 = false ∨ valuation q 1438 = false ∨ valuation q 1447 = true := counterClause978 (baseVal q)

theorem counterClause979 (q : Nat → Bool) : valuationOf q 1417 = false ∨ valuationOf q 1439 = false ∨ valuationOf q 1448 = true := by
  have hs : count1443 q = (countLit q [-2, -3, -5, -6, -12, -13, -15]) + (countLit q [-16, -19, -20, -22, -24, -25, -26]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -6, -12, -13, -15]) (l₂ := [-16, -19, -20, -22, -24, -25, -26])
  have hm := merge_two (literal (valuationOf q) (1417)) (literal (valuationOf q) (1439)) (literal (valuationOf q) (1448)) (countLit q [-2, -3, -5, -6, -12, -13, -15]) (countLit q [-16, -19, -20, -22, -24, -25, -26]) (count1443 q) 2 4 (meaning1417 q) (meaning1439 q) (meaning1448 q) hs
  change valuationOf q 1417 = false ∨ valuationOf q 1439 = false ∨ valuationOf q 1448 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause979 (q : Snake 81) (h : Conditions q) : valuation q 1417 = false ∨ valuation q 1439 = false ∨ valuation q 1448 = true := counterClause979 (baseVal q)

theorem counterClause980 (q : Nat → Bool) : valuationOf q 1417 = false ∨ valuationOf q 1440 = false ∨ valuationOf q 1449 = true := by
  have hs : count1443 q = (countLit q [-2, -3, -5, -6, -12, -13, -15]) + (countLit q [-16, -19, -20, -22, -24, -25, -26]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -6, -12, -13, -15]) (l₂ := [-16, -19, -20, -22, -24, -25, -26])
  have hm := merge_two (literal (valuationOf q) (1417)) (literal (valuationOf q) (1440)) (literal (valuationOf q) (1449)) (countLit q [-2, -3, -5, -6, -12, -13, -15]) (countLit q [-16, -19, -20, -22, -24, -25, -26]) (count1443 q) 2 5 (meaning1417 q) (meaning1440 q) (meaning1449 q) hs
  change valuationOf q 1417 = false ∨ valuationOf q 1440 = false ∨ valuationOf q 1449 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause980 (q : Snake 81) (h : Conditions q) : valuation q 1417 = false ∨ valuation q 1440 = false ∨ valuation q 1449 = true := counterClause980 (baseVal q)

theorem counterClause981 (q : Nat → Bool) : valuationOf q 1417 = false ∨ valuationOf q 1441 = false ∨ valuationOf q 1450 = true := by
  have hs : count1443 q = (countLit q [-2, -3, -5, -6, -12, -13, -15]) + (countLit q [-16, -19, -20, -22, -24, -25, -26]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -6, -12, -13, -15]) (l₂ := [-16, -19, -20, -22, -24, -25, -26])
  have hm := merge_two (literal (valuationOf q) (1417)) (literal (valuationOf q) (1441)) (literal (valuationOf q) (1450)) (countLit q [-2, -3, -5, -6, -12, -13, -15]) (countLit q [-16, -19, -20, -22, -24, -25, -26]) (count1443 q) 2 6 (meaning1417 q) (meaning1441 q) (meaning1450 q) hs
  change valuationOf q 1417 = false ∨ valuationOf q 1441 = false ∨ valuationOf q 1450 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause981 (q : Snake 81) (h : Conditions q) : valuation q 1417 = false ∨ valuation q 1441 = false ∨ valuation q 1450 = true := counterClause981 (baseVal q)

theorem counterClause982 (q : Nat → Bool) : valuationOf q 1418 = false ∨ valuationOf q 1437 = false ∨ valuationOf q 1447 = true := by
  have hs : count1443 q = (countLit q [-2, -3, -5, -6, -12, -13, -15]) + (countLit q [-16, -19, -20, -22, -24, -25, -26]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -6, -12, -13, -15]) (l₂ := [-16, -19, -20, -22, -24, -25, -26])
  have hm := merge_two (literal (valuationOf q) (1418)) (literal (valuationOf q) (1437)) (literal (valuationOf q) (1447)) (countLit q [-2, -3, -5, -6, -12, -13, -15]) (countLit q [-16, -19, -20, -22, -24, -25, -26]) (count1443 q) 3 2 (meaning1418 q) (meaning1437 q) (meaning1447 q) hs
  change valuationOf q 1418 = false ∨ valuationOf q 1437 = false ∨ valuationOf q 1447 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause982 (q : Snake 81) (h : Conditions q) : valuation q 1418 = false ∨ valuation q 1437 = false ∨ valuation q 1447 = true := counterClause982 (baseVal q)

theorem counterClause983 (q : Nat → Bool) : valuationOf q 1418 = false ∨ valuationOf q 1438 = false ∨ valuationOf q 1448 = true := by
  have hs : count1443 q = (countLit q [-2, -3, -5, -6, -12, -13, -15]) + (countLit q [-16, -19, -20, -22, -24, -25, -26]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -6, -12, -13, -15]) (l₂ := [-16, -19, -20, -22, -24, -25, -26])
  have hm := merge_two (literal (valuationOf q) (1418)) (literal (valuationOf q) (1438)) (literal (valuationOf q) (1448)) (countLit q [-2, -3, -5, -6, -12, -13, -15]) (countLit q [-16, -19, -20, -22, -24, -25, -26]) (count1443 q) 3 3 (meaning1418 q) (meaning1438 q) (meaning1448 q) hs
  change valuationOf q 1418 = false ∨ valuationOf q 1438 = false ∨ valuationOf q 1448 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause983 (q : Snake 81) (h : Conditions q) : valuation q 1418 = false ∨ valuation q 1438 = false ∨ valuation q 1448 = true := counterClause983 (baseVal q)

theorem counterClause984 (q : Nat → Bool) : valuationOf q 1418 = false ∨ valuationOf q 1439 = false ∨ valuationOf q 1449 = true := by
  have hs : count1443 q = (countLit q [-2, -3, -5, -6, -12, -13, -15]) + (countLit q [-16, -19, -20, -22, -24, -25, -26]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -6, -12, -13, -15]) (l₂ := [-16, -19, -20, -22, -24, -25, -26])
  have hm := merge_two (literal (valuationOf q) (1418)) (literal (valuationOf q) (1439)) (literal (valuationOf q) (1449)) (countLit q [-2, -3, -5, -6, -12, -13, -15]) (countLit q [-16, -19, -20, -22, -24, -25, -26]) (count1443 q) 3 4 (meaning1418 q) (meaning1439 q) (meaning1449 q) hs
  change valuationOf q 1418 = false ∨ valuationOf q 1439 = false ∨ valuationOf q 1449 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause984 (q : Snake 81) (h : Conditions q) : valuation q 1418 = false ∨ valuation q 1439 = false ∨ valuation q 1449 = true := counterClause984 (baseVal q)

theorem counterClause985 (q : Nat → Bool) : valuationOf q 1419 = false ∨ valuationOf q 1437 = false ∨ valuationOf q 1448 = true := by
  have hs : count1443 q = (countLit q [-2, -3, -5, -6, -12, -13, -15]) + (countLit q [-16, -19, -20, -22, -24, -25, -26]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -6, -12, -13, -15]) (l₂ := [-16, -19, -20, -22, -24, -25, -26])
  have hm := merge_two (literal (valuationOf q) (1419)) (literal (valuationOf q) (1437)) (literal (valuationOf q) (1448)) (countLit q [-2, -3, -5, -6, -12, -13, -15]) (countLit q [-16, -19, -20, -22, -24, -25, -26]) (count1443 q) 4 2 (meaning1419 q) (meaning1437 q) (meaning1448 q) hs
  change valuationOf q 1419 = false ∨ valuationOf q 1437 = false ∨ valuationOf q 1448 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause985 (q : Snake 81) (h : Conditions q) : valuation q 1419 = false ∨ valuation q 1437 = false ∨ valuation q 1448 = true := counterClause985 (baseVal q)

theorem counterClause986 (q : Nat → Bool) : valuationOf q 1419 = false ∨ valuationOf q 1438 = false ∨ valuationOf q 1449 = true := by
  have hs : count1443 q = (countLit q [-2, -3, -5, -6, -12, -13, -15]) + (countLit q [-16, -19, -20, -22, -24, -25, -26]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -6, -12, -13, -15]) (l₂ := [-16, -19, -20, -22, -24, -25, -26])
  have hm := merge_two (literal (valuationOf q) (1419)) (literal (valuationOf q) (1438)) (literal (valuationOf q) (1449)) (countLit q [-2, -3, -5, -6, -12, -13, -15]) (countLit q [-16, -19, -20, -22, -24, -25, -26]) (count1443 q) 4 3 (meaning1419 q) (meaning1438 q) (meaning1449 q) hs
  change valuationOf q 1419 = false ∨ valuationOf q 1438 = false ∨ valuationOf q 1449 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause986 (q : Snake 81) (h : Conditions q) : valuation q 1419 = false ∨ valuation q 1438 = false ∨ valuation q 1449 = true := counterClause986 (baseVal q)

theorem counterClause987 (q : Nat → Bool) : valuationOf q 1419 = false ∨ valuationOf q 1439 = false ∨ valuationOf q 1450 = true := by
  have hs : count1443 q = (countLit q [-2, -3, -5, -6, -12, -13, -15]) + (countLit q [-16, -19, -20, -22, -24, -25, -26]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -6, -12, -13, -15]) (l₂ := [-16, -19, -20, -22, -24, -25, -26])
  have hm := merge_two (literal (valuationOf q) (1419)) (literal (valuationOf q) (1439)) (literal (valuationOf q) (1450)) (countLit q [-2, -3, -5, -6, -12, -13, -15]) (countLit q [-16, -19, -20, -22, -24, -25, -26]) (count1443 q) 4 4 (meaning1419 q) (meaning1439 q) (meaning1450 q) hs
  change valuationOf q 1419 = false ∨ valuationOf q 1439 = false ∨ valuationOf q 1450 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause987 (q : Snake 81) (h : Conditions q) : valuation q 1419 = false ∨ valuation q 1439 = false ∨ valuation q 1450 = true := counterClause987 (baseVal q)

theorem counterClause988 (q : Nat → Bool) : valuationOf q 30 = true ∨ valuationOf q 1457 = true := by
  have hs : count1457 q = (countLit q [-29]) + (countLit q [-30]) := List.countP_append (p := literal q) (l₁ := [-29]) (l₂ := [-30])
  have hm := merge_right (literal (valuationOf q) (-30)) (literal (valuationOf q) (1457)) (countLit q [-29]) (countLit q [-30]) (count1457 q) 1 (meaningNeg30 q) (meaning1457 q) hs
  change (! (valuationOf q 30)) = false ∨ valuationOf q 1457 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause988 (q : Snake 81) (h : Conditions q) : valuation q 30 = true ∨ valuation q 1457 = true := counterClause988 (baseVal q)

theorem counterClause989 (q : Nat → Bool) : valuationOf q 29 = true ∨ valuationOf q 1457 = true := by
  have hs : count1457 q = (countLit q [-29]) + (countLit q [-30]) := List.countP_append (p := literal q) (l₁ := [-29]) (l₂ := [-30])
  have hm := merge_left (literal (valuationOf q) (-29)) (literal (valuationOf q) (1457)) (countLit q [-29]) (countLit q [-30]) (count1457 q) 1 (meaningNeg29 q) (meaning1457 q) hs
  change (! (valuationOf q 29)) = false ∨ valuationOf q 1457 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause989 (q : Snake 81) (h : Conditions q) : valuation q 29 = true ∨ valuation q 1457 = true := counterClause989 (baseVal q)

theorem counterClause990 (q : Nat → Bool) : valuationOf q 29 = true ∨ valuationOf q 30 = true ∨ valuationOf q 1458 = true := by
  have hs : count1457 q = (countLit q [-29]) + (countLit q [-30]) := List.countP_append (p := literal q) (l₁ := [-29]) (l₂ := [-30])
  have hm := merge_two (literal (valuationOf q) (-29)) (literal (valuationOf q) (-30)) (literal (valuationOf q) (1458)) (countLit q [-29]) (countLit q [-30]) (count1457 q) 1 1 (meaningNeg29 q) (meaningNeg30 q) (meaning1458 q) hs
  change (! (valuationOf q 29)) = false ∨ (! (valuationOf q 30)) = false ∨ valuationOf q 1458 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause990 (q : Snake 81) (h : Conditions q) : valuation q 29 = true ∨ valuation q 30 = true ∨ valuation q 1458 = true := counterClause990 (baseVal q)

theorem counterClause991 (q : Nat → Bool) : valuationOf q 27 = true ∨ valuationOf q 1459 = true := by
  have hs : count1459 q = (countLit q [-27]) + (countLit q [-29, -30]) := List.countP_append (p := literal q) (l₁ := [-27]) (l₂ := [-29, -30])
  have hm := merge_left (literal (valuationOf q) (-27)) (literal (valuationOf q) (1459)) (countLit q [-27]) (countLit q [-29, -30]) (count1459 q) 1 (meaningNeg27 q) (meaning1459 q) hs
  change (! (valuationOf q 27)) = false ∨ valuationOf q 1459 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause991 (q : Snake 81) (h : Conditions q) : valuation q 27 = true ∨ valuation q 1459 = true := counterClause991 (baseVal q)

theorem counterClause992 (q : Nat → Bool) : valuationOf q 27 = true ∨ valuationOf q 1457 = false ∨ valuationOf q 1460 = true := by
  have hs : count1459 q = (countLit q [-27]) + (countLit q [-29, -30]) := List.countP_append (p := literal q) (l₁ := [-27]) (l₂ := [-29, -30])
  have hm := merge_two (literal (valuationOf q) (-27)) (literal (valuationOf q) (1457)) (literal (valuationOf q) (1460)) (countLit q [-27]) (countLit q [-29, -30]) (count1459 q) 1 1 (meaningNeg27 q) (meaning1457 q) (meaning1460 q) hs
  change (! (valuationOf q 27)) = false ∨ valuationOf q 1457 = false ∨ valuationOf q 1460 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause992 (q : Snake 81) (h : Conditions q) : valuation q 27 = true ∨ valuation q 1457 = false ∨ valuation q 1460 = true := counterClause992 (baseVal q)

theorem block30 (q : Snake 81) (h : Conditions q) : B112E064.Block30 (valuation q) :=
  ⟨clause961 q h, clause962 q h, clause963 q h, clause964 q h, clause965 q h, clause966 q h, clause967 q h, clause968 q h, clause969 q h, clause970 q h, clause971 q h, clause972 q h, clause973 q h, clause974 q h, clause975 q h, clause976 q h, clause977 q h, clause978 q h, clause979 q h, clause980 q h, clause981 q h, clause982 q h, clause983 q h, clause984 q h, clause985 q h, clause986 q h, clause987 q h, clause988 q h, clause989 q h, clause990 q h, clause991 q h, clause992 q h⟩

end
end Snake9.Regrowth.E112064
