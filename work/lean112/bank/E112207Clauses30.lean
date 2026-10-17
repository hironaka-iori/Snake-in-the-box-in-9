import E112207Semantics
import B112E207Inputs
namespace Snake9.Regrowth.E112207
noncomputable section
local instance blockDec30 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause961 (q : Nat → Bool) : valuationOf q 1441 = false ∨ valuationOf q 1445 = true := by
  have hs : count1444 q = (countLit q [-15, -18, -21]) + (countLit q [-22, -23, -25, -27]) := List.countP_append (p := literal q) (l₁ := [-15, -18, -21]) (l₂ := [-22, -23, -25, -27])
  have hm := merge_right (literal (valuationOf q) (1441)) (literal (valuationOf q) (1445)) (countLit q [-15, -18, -21]) (countLit q [-22, -23, -25, -27]) (count1444 q) 2 (meaning1441 q) (meaning1445 q) hs
  change valuationOf q 1441 = false ∨ valuationOf q 1445 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause961 (q : Snake 81) (h : Conditions q) : valuation q 1441 = false ∨ valuation q 1445 = true := counterClause961 (baseVal q)

theorem counterClause962 (q : Nat → Bool) : valuationOf q 1443 = false ∨ valuationOf q 1447 = true := by
  have hs : count1444 q = (countLit q [-15, -18, -21]) + (countLit q [-22, -23, -25, -27]) := List.countP_append (p := literal q) (l₁ := [-15, -18, -21]) (l₂ := [-22, -23, -25, -27])
  have hm := merge_right (literal (valuationOf q) (1443)) (literal (valuationOf q) (1447)) (countLit q [-15, -18, -21]) (countLit q [-22, -23, -25, -27]) (count1444 q) 4 (meaning1443 q) (meaning1447 q) hs
  change valuationOf q 1443 = false ∨ valuationOf q 1447 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause962 (q : Snake 81) (h : Conditions q) : valuation q 1443 = false ∨ valuation q 1447 = true := counterClause962 (baseVal q)

theorem counterClause963 (q : Nat → Bool) : valuationOf q 1433 = false ∨ valuationOf q 1444 = true := by
  have hs : count1444 q = (countLit q [-15, -18, -21]) + (countLit q [-22, -23, -25, -27]) := List.countP_append (p := literal q) (l₁ := [-15, -18, -21]) (l₂ := [-22, -23, -25, -27])
  have hm := merge_left (literal (valuationOf q) (1433)) (literal (valuationOf q) (1444)) (countLit q [-15, -18, -21]) (countLit q [-22, -23, -25, -27]) (count1444 q) 1 (meaning1433 q) (meaning1444 q) hs
  change valuationOf q 1433 = false ∨ valuationOf q 1444 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause963 (q : Snake 81) (h : Conditions q) : valuation q 1433 = false ∨ valuation q 1444 = true := counterClause963 (baseVal q)

theorem counterClause964 (q : Nat → Bool) : valuationOf q 1433 = false ∨ valuationOf q 1440 = false ∨ valuationOf q 1445 = true := by
  have hs : count1444 q = (countLit q [-15, -18, -21]) + (countLit q [-22, -23, -25, -27]) := List.countP_append (p := literal q) (l₁ := [-15, -18, -21]) (l₂ := [-22, -23, -25, -27])
  have hm := merge_two (literal (valuationOf q) (1433)) (literal (valuationOf q) (1440)) (literal (valuationOf q) (1445)) (countLit q [-15, -18, -21]) (countLit q [-22, -23, -25, -27]) (count1444 q) 1 1 (meaning1433 q) (meaning1440 q) (meaning1445 q) hs
  change valuationOf q 1433 = false ∨ valuationOf q 1440 = false ∨ valuationOf q 1445 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause964 (q : Snake 81) (h : Conditions q) : valuation q 1433 = false ∨ valuation q 1440 = false ∨ valuation q 1445 = true := counterClause964 (baseVal q)

theorem counterClause965 (q : Nat → Bool) : valuationOf q 1433 = false ∨ valuationOf q 1441 = false ∨ valuationOf q 1446 = true := by
  have hs : count1444 q = (countLit q [-15, -18, -21]) + (countLit q [-22, -23, -25, -27]) := List.countP_append (p := literal q) (l₁ := [-15, -18, -21]) (l₂ := [-22, -23, -25, -27])
  have hm := merge_two (literal (valuationOf q) (1433)) (literal (valuationOf q) (1441)) (literal (valuationOf q) (1446)) (countLit q [-15, -18, -21]) (countLit q [-22, -23, -25, -27]) (count1444 q) 1 2 (meaning1433 q) (meaning1441 q) (meaning1446 q) hs
  change valuationOf q 1433 = false ∨ valuationOf q 1441 = false ∨ valuationOf q 1446 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause965 (q : Snake 81) (h : Conditions q) : valuation q 1433 = false ∨ valuation q 1441 = false ∨ valuation q 1446 = true := counterClause965 (baseVal q)

theorem counterClause966 (q : Nat → Bool) : valuationOf q 1433 = false ∨ valuationOf q 1442 = false ∨ valuationOf q 1447 = true := by
  have hs : count1444 q = (countLit q [-15, -18, -21]) + (countLit q [-22, -23, -25, -27]) := List.countP_append (p := literal q) (l₁ := [-15, -18, -21]) (l₂ := [-22, -23, -25, -27])
  have hm := merge_two (literal (valuationOf q) (1433)) (literal (valuationOf q) (1442)) (literal (valuationOf q) (1447)) (countLit q [-15, -18, -21]) (countLit q [-22, -23, -25, -27]) (count1444 q) 1 3 (meaning1433 q) (meaning1442 q) (meaning1447 q) hs
  change valuationOf q 1433 = false ∨ valuationOf q 1442 = false ∨ valuationOf q 1447 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause966 (q : Snake 81) (h : Conditions q) : valuation q 1433 = false ∨ valuation q 1442 = false ∨ valuation q 1447 = true := counterClause966 (baseVal q)

theorem counterClause967 (q : Nat → Bool) : valuationOf q 1433 = false ∨ valuationOf q 1443 = false ∨ valuationOf q 1448 = true := by
  have hs : count1444 q = (countLit q [-15, -18, -21]) + (countLit q [-22, -23, -25, -27]) := List.countP_append (p := literal q) (l₁ := [-15, -18, -21]) (l₂ := [-22, -23, -25, -27])
  have hm := merge_two (literal (valuationOf q) (1433)) (literal (valuationOf q) (1443)) (literal (valuationOf q) (1448)) (countLit q [-15, -18, -21]) (countLit q [-22, -23, -25, -27]) (count1444 q) 1 4 (meaning1433 q) (meaning1443 q) (meaning1448 q) hs
  change valuationOf q 1433 = false ∨ valuationOf q 1443 = false ∨ valuationOf q 1448 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause967 (q : Snake 81) (h : Conditions q) : valuation q 1433 = false ∨ valuation q 1443 = false ∨ valuation q 1448 = true := counterClause967 (baseVal q)

theorem counterClause968 (q : Nat → Bool) : valuationOf q 1434 = false ∨ valuationOf q 1445 = true := by
  have hs : count1444 q = (countLit q [-15, -18, -21]) + (countLit q [-22, -23, -25, -27]) := List.countP_append (p := literal q) (l₁ := [-15, -18, -21]) (l₂ := [-22, -23, -25, -27])
  have hm := merge_left (literal (valuationOf q) (1434)) (literal (valuationOf q) (1445)) (countLit q [-15, -18, -21]) (countLit q [-22, -23, -25, -27]) (count1444 q) 2 (meaning1434 q) (meaning1445 q) hs
  change valuationOf q 1434 = false ∨ valuationOf q 1445 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause968 (q : Snake 81) (h : Conditions q) : valuation q 1434 = false ∨ valuation q 1445 = true := counterClause968 (baseVal q)

theorem counterClause969 (q : Nat → Bool) : valuationOf q 1434 = false ∨ valuationOf q 1440 = false ∨ valuationOf q 1446 = true := by
  have hs : count1444 q = (countLit q [-15, -18, -21]) + (countLit q [-22, -23, -25, -27]) := List.countP_append (p := literal q) (l₁ := [-15, -18, -21]) (l₂ := [-22, -23, -25, -27])
  have hm := merge_two (literal (valuationOf q) (1434)) (literal (valuationOf q) (1440)) (literal (valuationOf q) (1446)) (countLit q [-15, -18, -21]) (countLit q [-22, -23, -25, -27]) (count1444 q) 2 1 (meaning1434 q) (meaning1440 q) (meaning1446 q) hs
  change valuationOf q 1434 = false ∨ valuationOf q 1440 = false ∨ valuationOf q 1446 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause969 (q : Snake 81) (h : Conditions q) : valuation q 1434 = false ∨ valuation q 1440 = false ∨ valuation q 1446 = true := counterClause969 (baseVal q)

theorem counterClause970 (q : Nat → Bool) : valuationOf q 1434 = false ∨ valuationOf q 1441 = false ∨ valuationOf q 1447 = true := by
  have hs : count1444 q = (countLit q [-15, -18, -21]) + (countLit q [-22, -23, -25, -27]) := List.countP_append (p := literal q) (l₁ := [-15, -18, -21]) (l₂ := [-22, -23, -25, -27])
  have hm := merge_two (literal (valuationOf q) (1434)) (literal (valuationOf q) (1441)) (literal (valuationOf q) (1447)) (countLit q [-15, -18, -21]) (countLit q [-22, -23, -25, -27]) (count1444 q) 2 2 (meaning1434 q) (meaning1441 q) (meaning1447 q) hs
  change valuationOf q 1434 = false ∨ valuationOf q 1441 = false ∨ valuationOf q 1447 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause970 (q : Snake 81) (h : Conditions q) : valuation q 1434 = false ∨ valuation q 1441 = false ∨ valuation q 1447 = true := counterClause970 (baseVal q)

theorem counterClause971 (q : Nat → Bool) : valuationOf q 1434 = false ∨ valuationOf q 1442 = false ∨ valuationOf q 1448 = true := by
  have hs : count1444 q = (countLit q [-15, -18, -21]) + (countLit q [-22, -23, -25, -27]) := List.countP_append (p := literal q) (l₁ := [-15, -18, -21]) (l₂ := [-22, -23, -25, -27])
  have hm := merge_two (literal (valuationOf q) (1434)) (literal (valuationOf q) (1442)) (literal (valuationOf q) (1448)) (countLit q [-15, -18, -21]) (countLit q [-22, -23, -25, -27]) (count1444 q) 2 3 (meaning1434 q) (meaning1442 q) (meaning1448 q) hs
  change valuationOf q 1434 = false ∨ valuationOf q 1442 = false ∨ valuationOf q 1448 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause971 (q : Snake 81) (h : Conditions q) : valuation q 1434 = false ∨ valuation q 1442 = false ∨ valuation q 1448 = true := counterClause971 (baseVal q)

theorem counterClause972 (q : Nat → Bool) : valuationOf q 1434 = false ∨ valuationOf q 1443 = false ∨ valuationOf q 1449 = true := by
  have hs : count1444 q = (countLit q [-15, -18, -21]) + (countLit q [-22, -23, -25, -27]) := List.countP_append (p := literal q) (l₁ := [-15, -18, -21]) (l₂ := [-22, -23, -25, -27])
  have hm := merge_two (literal (valuationOf q) (1434)) (literal (valuationOf q) (1443)) (literal (valuationOf q) (1449)) (countLit q [-15, -18, -21]) (countLit q [-22, -23, -25, -27]) (count1444 q) 2 4 (meaning1434 q) (meaning1443 q) (meaning1449 q) hs
  change valuationOf q 1434 = false ∨ valuationOf q 1443 = false ∨ valuationOf q 1449 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause972 (q : Snake 81) (h : Conditions q) : valuation q 1434 = false ∨ valuation q 1443 = false ∨ valuation q 1449 = true := counterClause972 (baseVal q)

theorem counterClause973 (q : Nat → Bool) : valuationOf q 1435 = false ∨ valuationOf q 1446 = true := by
  have hs : count1444 q = (countLit q [-15, -18, -21]) + (countLit q [-22, -23, -25, -27]) := List.countP_append (p := literal q) (l₁ := [-15, -18, -21]) (l₂ := [-22, -23, -25, -27])
  have hm := merge_left (literal (valuationOf q) (1435)) (literal (valuationOf q) (1446)) (countLit q [-15, -18, -21]) (countLit q [-22, -23, -25, -27]) (count1444 q) 3 (meaning1435 q) (meaning1446 q) hs
  change valuationOf q 1435 = false ∨ valuationOf q 1446 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause973 (q : Snake 81) (h : Conditions q) : valuation q 1435 = false ∨ valuation q 1446 = true := counterClause973 (baseVal q)

theorem counterClause974 (q : Nat → Bool) : valuationOf q 1435 = false ∨ valuationOf q 1440 = false ∨ valuationOf q 1447 = true := by
  have hs : count1444 q = (countLit q [-15, -18, -21]) + (countLit q [-22, -23, -25, -27]) := List.countP_append (p := literal q) (l₁ := [-15, -18, -21]) (l₂ := [-22, -23, -25, -27])
  have hm := merge_two (literal (valuationOf q) (1435)) (literal (valuationOf q) (1440)) (literal (valuationOf q) (1447)) (countLit q [-15, -18, -21]) (countLit q [-22, -23, -25, -27]) (count1444 q) 3 1 (meaning1435 q) (meaning1440 q) (meaning1447 q) hs
  change valuationOf q 1435 = false ∨ valuationOf q 1440 = false ∨ valuationOf q 1447 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause974 (q : Snake 81) (h : Conditions q) : valuation q 1435 = false ∨ valuation q 1440 = false ∨ valuation q 1447 = true := counterClause974 (baseVal q)

theorem counterClause975 (q : Nat → Bool) : valuationOf q 1435 = false ∨ valuationOf q 1441 = false ∨ valuationOf q 1448 = true := by
  have hs : count1444 q = (countLit q [-15, -18, -21]) + (countLit q [-22, -23, -25, -27]) := List.countP_append (p := literal q) (l₁ := [-15, -18, -21]) (l₂ := [-22, -23, -25, -27])
  have hm := merge_two (literal (valuationOf q) (1435)) (literal (valuationOf q) (1441)) (literal (valuationOf q) (1448)) (countLit q [-15, -18, -21]) (countLit q [-22, -23, -25, -27]) (count1444 q) 3 2 (meaning1435 q) (meaning1441 q) (meaning1448 q) hs
  change valuationOf q 1435 = false ∨ valuationOf q 1441 = false ∨ valuationOf q 1448 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause975 (q : Snake 81) (h : Conditions q) : valuation q 1435 = false ∨ valuation q 1441 = false ∨ valuation q 1448 = true := counterClause975 (baseVal q)

theorem counterClause976 (q : Nat → Bool) : valuationOf q 1435 = false ∨ valuationOf q 1442 = false ∨ valuationOf q 1449 = true := by
  have hs : count1444 q = (countLit q [-15, -18, -21]) + (countLit q [-22, -23, -25, -27]) := List.countP_append (p := literal q) (l₁ := [-15, -18, -21]) (l₂ := [-22, -23, -25, -27])
  have hm := merge_two (literal (valuationOf q) (1435)) (literal (valuationOf q) (1442)) (literal (valuationOf q) (1449)) (countLit q [-15, -18, -21]) (countLit q [-22, -23, -25, -27]) (count1444 q) 3 3 (meaning1435 q) (meaning1442 q) (meaning1449 q) hs
  change valuationOf q 1435 = false ∨ valuationOf q 1442 = false ∨ valuationOf q 1449 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause976 (q : Snake 81) (h : Conditions q) : valuation q 1435 = false ∨ valuation q 1442 = false ∨ valuation q 1449 = true := counterClause976 (baseVal q)

theorem counterClause977 (q : Nat → Bool) : valuationOf q 1444 = false ∨ valuationOf q 1451 = true := by
  have hs : count1451 q = (countLit q [-2, -4, -5, -6, -10, -11, -12]) + (countLit q [-15, -18, -21, -22, -23, -25, -27]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5, -6, -10, -11, -12]) (l₂ := [-15, -18, -21, -22, -23, -25, -27])
  have hm := merge_right (literal (valuationOf q) (1444)) (literal (valuationOf q) (1451)) (countLit q [-2, -4, -5, -6, -10, -11, -12]) (countLit q [-15, -18, -21, -22, -23, -25, -27]) (count1451 q) 1 (meaning1444 q) (meaning1451 q) hs
  change valuationOf q 1444 = false ∨ valuationOf q 1451 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause977 (q : Snake 81) (h : Conditions q) : valuation q 1444 = false ∨ valuation q 1451 = true := counterClause977 (baseVal q)

theorem counterClause978 (q : Nat → Bool) : valuationOf q 1445 = false ∨ valuationOf q 1452 = true := by
  have hs : count1451 q = (countLit q [-2, -4, -5, -6, -10, -11, -12]) + (countLit q [-15, -18, -21, -22, -23, -25, -27]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5, -6, -10, -11, -12]) (l₂ := [-15, -18, -21, -22, -23, -25, -27])
  have hm := merge_right (literal (valuationOf q) (1445)) (literal (valuationOf q) (1452)) (countLit q [-2, -4, -5, -6, -10, -11, -12]) (countLit q [-15, -18, -21, -22, -23, -25, -27]) (count1451 q) 2 (meaning1445 q) (meaning1452 q) hs
  change valuationOf q 1445 = false ∨ valuationOf q 1452 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause978 (q : Snake 81) (h : Conditions q) : valuation q 1445 = false ∨ valuation q 1452 = true := counterClause978 (baseVal q)

theorem counterClause979 (q : Nat → Bool) : valuationOf q 1446 = false ∨ valuationOf q 1453 = true := by
  have hs : count1451 q = (countLit q [-2, -4, -5, -6, -10, -11, -12]) + (countLit q [-15, -18, -21, -22, -23, -25, -27]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5, -6, -10, -11, -12]) (l₂ := [-15, -18, -21, -22, -23, -25, -27])
  have hm := merge_right (literal (valuationOf q) (1446)) (literal (valuationOf q) (1453)) (countLit q [-2, -4, -5, -6, -10, -11, -12]) (countLit q [-15, -18, -21, -22, -23, -25, -27]) (count1451 q) 3 (meaning1446 q) (meaning1453 q) hs
  change valuationOf q 1446 = false ∨ valuationOf q 1453 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause979 (q : Snake 81) (h : Conditions q) : valuation q 1446 = false ∨ valuation q 1453 = true := counterClause979 (baseVal q)

theorem counterClause980 (q : Nat → Bool) : valuationOf q 1447 = false ∨ valuationOf q 1454 = true := by
  have hs : count1451 q = (countLit q [-2, -4, -5, -6, -10, -11, -12]) + (countLit q [-15, -18, -21, -22, -23, -25, -27]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5, -6, -10, -11, -12]) (l₂ := [-15, -18, -21, -22, -23, -25, -27])
  have hm := merge_right (literal (valuationOf q) (1447)) (literal (valuationOf q) (1454)) (countLit q [-2, -4, -5, -6, -10, -11, -12]) (countLit q [-15, -18, -21, -22, -23, -25, -27]) (count1451 q) 4 (meaning1447 q) (meaning1454 q) hs
  change valuationOf q 1447 = false ∨ valuationOf q 1454 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause980 (q : Snake 81) (h : Conditions q) : valuation q 1447 = false ∨ valuation q 1454 = true := counterClause980 (baseVal q)

theorem counterClause981 (q : Nat → Bool) : valuationOf q 1448 = false ∨ valuationOf q 1455 = true := by
  have hs : count1451 q = (countLit q [-2, -4, -5, -6, -10, -11, -12]) + (countLit q [-15, -18, -21, -22, -23, -25, -27]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5, -6, -10, -11, -12]) (l₂ := [-15, -18, -21, -22, -23, -25, -27])
  have hm := merge_right (literal (valuationOf q) (1448)) (literal (valuationOf q) (1455)) (countLit q [-2, -4, -5, -6, -10, -11, -12]) (countLit q [-15, -18, -21, -22, -23, -25, -27]) (count1451 q) 5 (meaning1448 q) (meaning1455 q) hs
  change valuationOf q 1448 = false ∨ valuationOf q 1455 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause981 (q : Snake 81) (h : Conditions q) : valuation q 1448 = false ∨ valuation q 1455 = true := counterClause981 (baseVal q)

theorem counterClause982 (q : Nat → Bool) : valuationOf q 1449 = false ∨ valuationOf q 1456 = true := by
  have hs : count1451 q = (countLit q [-2, -4, -5, -6, -10, -11, -12]) + (countLit q [-15, -18, -21, -22, -23, -25, -27]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5, -6, -10, -11, -12]) (l₂ := [-15, -18, -21, -22, -23, -25, -27])
  have hm := merge_right (literal (valuationOf q) (1449)) (literal (valuationOf q) (1456)) (countLit q [-2, -4, -5, -6, -10, -11, -12]) (countLit q [-15, -18, -21, -22, -23, -25, -27]) (count1451 q) 6 (meaning1449 q) (meaning1456 q) hs
  change valuationOf q 1449 = false ∨ valuationOf q 1456 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause982 (q : Snake 81) (h : Conditions q) : valuation q 1449 = false ∨ valuation q 1456 = true := counterClause982 (baseVal q)

theorem counterClause983 (q : Nat → Bool) : valuationOf q 1424 = false ∨ valuationOf q 1444 = false ∨ valuationOf q 1452 = true := by
  have hs : count1451 q = (countLit q [-2, -4, -5, -6, -10, -11, -12]) + (countLit q [-15, -18, -21, -22, -23, -25, -27]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5, -6, -10, -11, -12]) (l₂ := [-15, -18, -21, -22, -23, -25, -27])
  have hm := merge_two (literal (valuationOf q) (1424)) (literal (valuationOf q) (1444)) (literal (valuationOf q) (1452)) (countLit q [-2, -4, -5, -6, -10, -11, -12]) (countLit q [-15, -18, -21, -22, -23, -25, -27]) (count1451 q) 1 1 (meaning1424 q) (meaning1444 q) (meaning1452 q) hs
  change valuationOf q 1424 = false ∨ valuationOf q 1444 = false ∨ valuationOf q 1452 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause983 (q : Snake 81) (h : Conditions q) : valuation q 1424 = false ∨ valuation q 1444 = false ∨ valuation q 1452 = true := counterClause983 (baseVal q)

theorem counterClause984 (q : Nat → Bool) : valuationOf q 1424 = false ∨ valuationOf q 1445 = false ∨ valuationOf q 1453 = true := by
  have hs : count1451 q = (countLit q [-2, -4, -5, -6, -10, -11, -12]) + (countLit q [-15, -18, -21, -22, -23, -25, -27]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5, -6, -10, -11, -12]) (l₂ := [-15, -18, -21, -22, -23, -25, -27])
  have hm := merge_two (literal (valuationOf q) (1424)) (literal (valuationOf q) (1445)) (literal (valuationOf q) (1453)) (countLit q [-2, -4, -5, -6, -10, -11, -12]) (countLit q [-15, -18, -21, -22, -23, -25, -27]) (count1451 q) 1 2 (meaning1424 q) (meaning1445 q) (meaning1453 q) hs
  change valuationOf q 1424 = false ∨ valuationOf q 1445 = false ∨ valuationOf q 1453 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause984 (q : Snake 81) (h : Conditions q) : valuation q 1424 = false ∨ valuation q 1445 = false ∨ valuation q 1453 = true := counterClause984 (baseVal q)

theorem counterClause985 (q : Nat → Bool) : valuationOf q 1424 = false ∨ valuationOf q 1446 = false ∨ valuationOf q 1454 = true := by
  have hs : count1451 q = (countLit q [-2, -4, -5, -6, -10, -11, -12]) + (countLit q [-15, -18, -21, -22, -23, -25, -27]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5, -6, -10, -11, -12]) (l₂ := [-15, -18, -21, -22, -23, -25, -27])
  have hm := merge_two (literal (valuationOf q) (1424)) (literal (valuationOf q) (1446)) (literal (valuationOf q) (1454)) (countLit q [-2, -4, -5, -6, -10, -11, -12]) (countLit q [-15, -18, -21, -22, -23, -25, -27]) (count1451 q) 1 3 (meaning1424 q) (meaning1446 q) (meaning1454 q) hs
  change valuationOf q 1424 = false ∨ valuationOf q 1446 = false ∨ valuationOf q 1454 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause985 (q : Snake 81) (h : Conditions q) : valuation q 1424 = false ∨ valuation q 1446 = false ∨ valuation q 1454 = true := counterClause985 (baseVal q)

theorem counterClause986 (q : Nat → Bool) : valuationOf q 1424 = false ∨ valuationOf q 1447 = false ∨ valuationOf q 1455 = true := by
  have hs : count1451 q = (countLit q [-2, -4, -5, -6, -10, -11, -12]) + (countLit q [-15, -18, -21, -22, -23, -25, -27]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5, -6, -10, -11, -12]) (l₂ := [-15, -18, -21, -22, -23, -25, -27])
  have hm := merge_two (literal (valuationOf q) (1424)) (literal (valuationOf q) (1447)) (literal (valuationOf q) (1455)) (countLit q [-2, -4, -5, -6, -10, -11, -12]) (countLit q [-15, -18, -21, -22, -23, -25, -27]) (count1451 q) 1 4 (meaning1424 q) (meaning1447 q) (meaning1455 q) hs
  change valuationOf q 1424 = false ∨ valuationOf q 1447 = false ∨ valuationOf q 1455 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause986 (q : Snake 81) (h : Conditions q) : valuation q 1424 = false ∨ valuation q 1447 = false ∨ valuation q 1455 = true := counterClause986 (baseVal q)

theorem counterClause987 (q : Nat → Bool) : valuationOf q 1424 = false ∨ valuationOf q 1448 = false ∨ valuationOf q 1456 = true := by
  have hs : count1451 q = (countLit q [-2, -4, -5, -6, -10, -11, -12]) + (countLit q [-15, -18, -21, -22, -23, -25, -27]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5, -6, -10, -11, -12]) (l₂ := [-15, -18, -21, -22, -23, -25, -27])
  have hm := merge_two (literal (valuationOf q) (1424)) (literal (valuationOf q) (1448)) (literal (valuationOf q) (1456)) (countLit q [-2, -4, -5, -6, -10, -11, -12]) (countLit q [-15, -18, -21, -22, -23, -25, -27]) (count1451 q) 1 5 (meaning1424 q) (meaning1448 q) (meaning1456 q) hs
  change valuationOf q 1424 = false ∨ valuationOf q 1448 = false ∨ valuationOf q 1456 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause987 (q : Snake 81) (h : Conditions q) : valuation q 1424 = false ∨ valuation q 1448 = false ∨ valuation q 1456 = true := counterClause987 (baseVal q)

theorem counterClause988 (q : Nat → Bool) : valuationOf q 1424 = false ∨ valuationOf q 1449 = false ∨ valuationOf q 1457 = true := by
  have hs : count1451 q = (countLit q [-2, -4, -5, -6, -10, -11, -12]) + (countLit q [-15, -18, -21, -22, -23, -25, -27]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5, -6, -10, -11, -12]) (l₂ := [-15, -18, -21, -22, -23, -25, -27])
  have hm := merge_two (literal (valuationOf q) (1424)) (literal (valuationOf q) (1449)) (literal (valuationOf q) (1457)) (countLit q [-2, -4, -5, -6, -10, -11, -12]) (countLit q [-15, -18, -21, -22, -23, -25, -27]) (count1451 q) 1 6 (meaning1424 q) (meaning1449 q) (meaning1457 q) hs
  change valuationOf q 1424 = false ∨ valuationOf q 1449 = false ∨ valuationOf q 1457 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause988 (q : Snake 81) (h : Conditions q) : valuation q 1424 = false ∨ valuation q 1449 = false ∨ valuation q 1457 = true := counterClause988 (baseVal q)

theorem counterClause989 (q : Nat → Bool) : valuationOf q 1425 = false ∨ valuationOf q 1452 = true := by
  have hs : count1451 q = (countLit q [-2, -4, -5, -6, -10, -11, -12]) + (countLit q [-15, -18, -21, -22, -23, -25, -27]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5, -6, -10, -11, -12]) (l₂ := [-15, -18, -21, -22, -23, -25, -27])
  have hm := merge_left (literal (valuationOf q) (1425)) (literal (valuationOf q) (1452)) (countLit q [-2, -4, -5, -6, -10, -11, -12]) (countLit q [-15, -18, -21, -22, -23, -25, -27]) (count1451 q) 2 (meaning1425 q) (meaning1452 q) hs
  change valuationOf q 1425 = false ∨ valuationOf q 1452 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause989 (q : Snake 81) (h : Conditions q) : valuation q 1425 = false ∨ valuation q 1452 = true := counterClause989 (baseVal q)

theorem counterClause990 (q : Nat → Bool) : valuationOf q 1425 = false ∨ valuationOf q 1444 = false ∨ valuationOf q 1453 = true := by
  have hs : count1451 q = (countLit q [-2, -4, -5, -6, -10, -11, -12]) + (countLit q [-15, -18, -21, -22, -23, -25, -27]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5, -6, -10, -11, -12]) (l₂ := [-15, -18, -21, -22, -23, -25, -27])
  have hm := merge_two (literal (valuationOf q) (1425)) (literal (valuationOf q) (1444)) (literal (valuationOf q) (1453)) (countLit q [-2, -4, -5, -6, -10, -11, -12]) (countLit q [-15, -18, -21, -22, -23, -25, -27]) (count1451 q) 2 1 (meaning1425 q) (meaning1444 q) (meaning1453 q) hs
  change valuationOf q 1425 = false ∨ valuationOf q 1444 = false ∨ valuationOf q 1453 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause990 (q : Snake 81) (h : Conditions q) : valuation q 1425 = false ∨ valuation q 1444 = false ∨ valuation q 1453 = true := counterClause990 (baseVal q)

theorem counterClause991 (q : Nat → Bool) : valuationOf q 1425 = false ∨ valuationOf q 1445 = false ∨ valuationOf q 1454 = true := by
  have hs : count1451 q = (countLit q [-2, -4, -5, -6, -10, -11, -12]) + (countLit q [-15, -18, -21, -22, -23, -25, -27]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5, -6, -10, -11, -12]) (l₂ := [-15, -18, -21, -22, -23, -25, -27])
  have hm := merge_two (literal (valuationOf q) (1425)) (literal (valuationOf q) (1445)) (literal (valuationOf q) (1454)) (countLit q [-2, -4, -5, -6, -10, -11, -12]) (countLit q [-15, -18, -21, -22, -23, -25, -27]) (count1451 q) 2 2 (meaning1425 q) (meaning1445 q) (meaning1454 q) hs
  change valuationOf q 1425 = false ∨ valuationOf q 1445 = false ∨ valuationOf q 1454 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause991 (q : Snake 81) (h : Conditions q) : valuation q 1425 = false ∨ valuation q 1445 = false ∨ valuation q 1454 = true := counterClause991 (baseVal q)

theorem counterClause992 (q : Nat → Bool) : valuationOf q 1425 = false ∨ valuationOf q 1446 = false ∨ valuationOf q 1455 = true := by
  have hs : count1451 q = (countLit q [-2, -4, -5, -6, -10, -11, -12]) + (countLit q [-15, -18, -21, -22, -23, -25, -27]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5, -6, -10, -11, -12]) (l₂ := [-15, -18, -21, -22, -23, -25, -27])
  have hm := merge_two (literal (valuationOf q) (1425)) (literal (valuationOf q) (1446)) (literal (valuationOf q) (1455)) (countLit q [-2, -4, -5, -6, -10, -11, -12]) (countLit q [-15, -18, -21, -22, -23, -25, -27]) (count1451 q) 2 3 (meaning1425 q) (meaning1446 q) (meaning1455 q) hs
  change valuationOf q 1425 = false ∨ valuationOf q 1446 = false ∨ valuationOf q 1455 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause992 (q : Snake 81) (h : Conditions q) : valuation q 1425 = false ∨ valuation q 1446 = false ∨ valuation q 1455 = true := counterClause992 (baseVal q)

theorem block30 (q : Snake 81) (h : Conditions q) : B112E207.Block30 (valuation q) :=
  ⟨clause961 q h, clause962 q h, clause963 q h, clause964 q h, clause965 q h, clause966 q h, clause967 q h, clause968 q h, clause969 q h, clause970 q h, clause971 q h, clause972 q h, clause973 q h, clause974 q h, clause975 q h, clause976 q h, clause977 q h, clause978 q h, clause979 q h, clause980 q h, clause981 q h, clause982 q h, clause983 q h, clause984 q h, clause985 q h, clause986 q h, clause987 q h, clause988 q h, clause989 q h, clause990 q h, clause991 q h, clause992 q h⟩

end
end Snake9.Regrowth.E112207
