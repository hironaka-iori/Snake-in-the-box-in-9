import E112026Semantics
import B112E026Inputs
namespace Snake9.Regrowth.E112026
noncomputable section
local instance blockDec30 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause961 (q : Nat → Bool) : valuationOf q 1506 = false ∨ valuationOf q 1514 = false ∨ valuationOf q 1519 = true := by
  have hs : count1518 q = (countLit q [-28, -31, -33, -35]) + (countLit q [-36, -37, -39, -41]) := List.countP_append (p := literal q) (l₁ := [-28, -31, -33, -35]) (l₂ := [-36, -37, -39, -41])
  have hm := merge_two (literal (valuationOf q) (1506)) (literal (valuationOf q) (1514)) (literal (valuationOf q) (1519)) (countLit q [-28, -31, -33, -35]) (countLit q [-36, -37, -39, -41]) (count1518 q) 1 1 (meaning1506 q) (meaning1514 q) (meaning1519 q) hs
  change valuationOf q 1506 = false ∨ valuationOf q 1514 = false ∨ valuationOf q 1519 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause961 (q : Snake 81) (h : Conditions q) : valuation q 1506 = false ∨ valuation q 1514 = false ∨ valuation q 1519 = true := counterClause961 (baseVal q)

theorem counterClause962 (q : Nat → Bool) : valuationOf q 1506 = false ∨ valuationOf q 1515 = false ∨ valuationOf q 1520 = true := by
  have hs : count1518 q = (countLit q [-28, -31, -33, -35]) + (countLit q [-36, -37, -39, -41]) := List.countP_append (p := literal q) (l₁ := [-28, -31, -33, -35]) (l₂ := [-36, -37, -39, -41])
  have hm := merge_two (literal (valuationOf q) (1506)) (literal (valuationOf q) (1515)) (literal (valuationOf q) (1520)) (countLit q [-28, -31, -33, -35]) (countLit q [-36, -37, -39, -41]) (count1518 q) 1 2 (meaning1506 q) (meaning1515 q) (meaning1520 q) hs
  change valuationOf q 1506 = false ∨ valuationOf q 1515 = false ∨ valuationOf q 1520 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause962 (q : Snake 81) (h : Conditions q) : valuation q 1506 = false ∨ valuation q 1515 = false ∨ valuation q 1520 = true := counterClause962 (baseVal q)

theorem counterClause963 (q : Nat → Bool) : valuationOf q 1506 = false ∨ valuationOf q 1516 = false ∨ valuationOf q 1521 = true := by
  have hs : count1518 q = (countLit q [-28, -31, -33, -35]) + (countLit q [-36, -37, -39, -41]) := List.countP_append (p := literal q) (l₁ := [-28, -31, -33, -35]) (l₂ := [-36, -37, -39, -41])
  have hm := merge_two (literal (valuationOf q) (1506)) (literal (valuationOf q) (1516)) (literal (valuationOf q) (1521)) (countLit q [-28, -31, -33, -35]) (countLit q [-36, -37, -39, -41]) (count1518 q) 1 3 (meaning1506 q) (meaning1516 q) (meaning1521 q) hs
  change valuationOf q 1506 = false ∨ valuationOf q 1516 = false ∨ valuationOf q 1521 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause963 (q : Snake 81) (h : Conditions q) : valuation q 1506 = false ∨ valuation q 1516 = false ∨ valuation q 1521 = true := counterClause963 (baseVal q)

theorem counterClause964 (q : Nat → Bool) : valuationOf q 1506 = false ∨ valuationOf q 1517 = false ∨ valuationOf q 1522 = true := by
  have hs : count1518 q = (countLit q [-28, -31, -33, -35]) + (countLit q [-36, -37, -39, -41]) := List.countP_append (p := literal q) (l₁ := [-28, -31, -33, -35]) (l₂ := [-36, -37, -39, -41])
  have hm := merge_two (literal (valuationOf q) (1506)) (literal (valuationOf q) (1517)) (literal (valuationOf q) (1522)) (countLit q [-28, -31, -33, -35]) (countLit q [-36, -37, -39, -41]) (count1518 q) 1 4 (meaning1506 q) (meaning1517 q) (meaning1522 q) hs
  change valuationOf q 1506 = false ∨ valuationOf q 1517 = false ∨ valuationOf q 1522 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause964 (q : Snake 81) (h : Conditions q) : valuation q 1506 = false ∨ valuation q 1517 = false ∨ valuation q 1522 = true := counterClause964 (baseVal q)

theorem counterClause965 (q : Nat → Bool) : valuationOf q 1507 = false ∨ valuationOf q 1514 = false ∨ valuationOf q 1520 = true := by
  have hs : count1518 q = (countLit q [-28, -31, -33, -35]) + (countLit q [-36, -37, -39, -41]) := List.countP_append (p := literal q) (l₁ := [-28, -31, -33, -35]) (l₂ := [-36, -37, -39, -41])
  have hm := merge_two (literal (valuationOf q) (1507)) (literal (valuationOf q) (1514)) (literal (valuationOf q) (1520)) (countLit q [-28, -31, -33, -35]) (countLit q [-36, -37, -39, -41]) (count1518 q) 2 1 (meaning1507 q) (meaning1514 q) (meaning1520 q) hs
  change valuationOf q 1507 = false ∨ valuationOf q 1514 = false ∨ valuationOf q 1520 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause965 (q : Snake 81) (h : Conditions q) : valuation q 1507 = false ∨ valuation q 1514 = false ∨ valuation q 1520 = true := counterClause965 (baseVal q)

theorem counterClause966 (q : Nat → Bool) : valuationOf q 1507 = false ∨ valuationOf q 1515 = false ∨ valuationOf q 1521 = true := by
  have hs : count1518 q = (countLit q [-28, -31, -33, -35]) + (countLit q [-36, -37, -39, -41]) := List.countP_append (p := literal q) (l₁ := [-28, -31, -33, -35]) (l₂ := [-36, -37, -39, -41])
  have hm := merge_two (literal (valuationOf q) (1507)) (literal (valuationOf q) (1515)) (literal (valuationOf q) (1521)) (countLit q [-28, -31, -33, -35]) (countLit q [-36, -37, -39, -41]) (count1518 q) 2 2 (meaning1507 q) (meaning1515 q) (meaning1521 q) hs
  change valuationOf q 1507 = false ∨ valuationOf q 1515 = false ∨ valuationOf q 1521 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause966 (q : Snake 81) (h : Conditions q) : valuation q 1507 = false ∨ valuation q 1515 = false ∨ valuation q 1521 = true := counterClause966 (baseVal q)

theorem counterClause967 (q : Nat → Bool) : valuationOf q 1507 = false ∨ valuationOf q 1516 = false ∨ valuationOf q 1522 = true := by
  have hs : count1518 q = (countLit q [-28, -31, -33, -35]) + (countLit q [-36, -37, -39, -41]) := List.countP_append (p := literal q) (l₁ := [-28, -31, -33, -35]) (l₂ := [-36, -37, -39, -41])
  have hm := merge_two (literal (valuationOf q) (1507)) (literal (valuationOf q) (1516)) (literal (valuationOf q) (1522)) (countLit q [-28, -31, -33, -35]) (countLit q [-36, -37, -39, -41]) (count1518 q) 2 3 (meaning1507 q) (meaning1516 q) (meaning1522 q) hs
  change valuationOf q 1507 = false ∨ valuationOf q 1516 = false ∨ valuationOf q 1522 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause967 (q : Snake 81) (h : Conditions q) : valuation q 1507 = false ∨ valuation q 1516 = false ∨ valuation q 1522 = true := counterClause967 (baseVal q)

theorem counterClause968 (q : Nat → Bool) : valuationOf q 1508 = false ∨ valuationOf q 1514 = false ∨ valuationOf q 1521 = true := by
  have hs : count1518 q = (countLit q [-28, -31, -33, -35]) + (countLit q [-36, -37, -39, -41]) := List.countP_append (p := literal q) (l₁ := [-28, -31, -33, -35]) (l₂ := [-36, -37, -39, -41])
  have hm := merge_two (literal (valuationOf q) (1508)) (literal (valuationOf q) (1514)) (literal (valuationOf q) (1521)) (countLit q [-28, -31, -33, -35]) (countLit q [-36, -37, -39, -41]) (count1518 q) 3 1 (meaning1508 q) (meaning1514 q) (meaning1521 q) hs
  change valuationOf q 1508 = false ∨ valuationOf q 1514 = false ∨ valuationOf q 1521 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause968 (q : Snake 81) (h : Conditions q) : valuation q 1508 = false ∨ valuation q 1514 = false ∨ valuation q 1521 = true := counterClause968 (baseVal q)

theorem counterClause969 (q : Nat → Bool) : valuationOf q 1508 = false ∨ valuationOf q 1515 = false ∨ valuationOf q 1522 = true := by
  have hs : count1518 q = (countLit q [-28, -31, -33, -35]) + (countLit q [-36, -37, -39, -41]) := List.countP_append (p := literal q) (l₁ := [-28, -31, -33, -35]) (l₂ := [-36, -37, -39, -41])
  have hm := merge_two (literal (valuationOf q) (1508)) (literal (valuationOf q) (1515)) (literal (valuationOf q) (1522)) (countLit q [-28, -31, -33, -35]) (countLit q [-36, -37, -39, -41]) (count1518 q) 3 2 (meaning1508 q) (meaning1515 q) (meaning1522 q) hs
  change valuationOf q 1508 = false ∨ valuationOf q 1515 = false ∨ valuationOf q 1522 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause969 (q : Snake 81) (h : Conditions q) : valuation q 1508 = false ∨ valuation q 1515 = false ∨ valuation q 1522 = true := counterClause969 (baseVal q)

theorem counterClause970 (q : Nat → Bool) : valuationOf q 1509 = false ∨ valuationOf q 1514 = false ∨ valuationOf q 1522 = true := by
  have hs : count1518 q = (countLit q [-28, -31, -33, -35]) + (countLit q [-36, -37, -39, -41]) := List.countP_append (p := literal q) (l₁ := [-28, -31, -33, -35]) (l₂ := [-36, -37, -39, -41])
  have hm := merge_two (literal (valuationOf q) (1509)) (literal (valuationOf q) (1514)) (literal (valuationOf q) (1522)) (countLit q [-28, -31, -33, -35]) (countLit q [-36, -37, -39, -41]) (count1518 q) 4 1 (meaning1509 q) (meaning1514 q) (meaning1522 q) hs
  change valuationOf q 1509 = false ∨ valuationOf q 1514 = false ∨ valuationOf q 1522 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause970 (q : Snake 81) (h : Conditions q) : valuation q 1509 = false ∨ valuation q 1514 = false ∨ valuation q 1522 = true := counterClause970 (baseVal q)

theorem counterClause971 (q : Nat → Bool) : valuationOf q 44 = true ∨ valuationOf q 1526 = true := by
  have hs : count1526 q = (countLit q [-43]) + (countLit q [-44]) := List.countP_append (p := literal q) (l₁ := [-43]) (l₂ := [-44])
  have hm := merge_right (literal (valuationOf q) (-44)) (literal (valuationOf q) (1526)) (countLit q [-43]) (countLit q [-44]) (count1526 q) 1 (meaningNeg44 q) (meaning1526 q) hs
  change (! (valuationOf q 44)) = false ∨ valuationOf q 1526 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause971 (q : Snake 81) (h : Conditions q) : valuation q 44 = true ∨ valuation q 1526 = true := counterClause971 (baseVal q)

theorem counterClause972 (q : Nat → Bool) : valuationOf q 43 = true ∨ valuationOf q 1526 = true := by
  have hs : count1526 q = (countLit q [-43]) + (countLit q [-44]) := List.countP_append (p := literal q) (l₁ := [-43]) (l₂ := [-44])
  have hm := merge_left (literal (valuationOf q) (-43)) (literal (valuationOf q) (1526)) (countLit q [-43]) (countLit q [-44]) (count1526 q) 1 (meaningNeg43 q) (meaning1526 q) hs
  change (! (valuationOf q 43)) = false ∨ valuationOf q 1526 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause972 (q : Snake 81) (h : Conditions q) : valuation q 43 = true ∨ valuation q 1526 = true := counterClause972 (baseVal q)

theorem counterClause973 (q : Nat → Bool) : valuationOf q 43 = true ∨ valuationOf q 44 = true ∨ valuationOf q 1527 = true := by
  have hs : count1526 q = (countLit q [-43]) + (countLit q [-44]) := List.countP_append (p := literal q) (l₁ := [-43]) (l₂ := [-44])
  have hm := merge_two (literal (valuationOf q) (-43)) (literal (valuationOf q) (-44)) (literal (valuationOf q) (1527)) (countLit q [-43]) (countLit q [-44]) (count1526 q) 1 1 (meaningNeg43 q) (meaningNeg44 q) (meaning1527 q) hs
  change (! (valuationOf q 43)) = false ∨ (! (valuationOf q 44)) = false ∨ valuationOf q 1527 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause973 (q : Snake 81) (h : Conditions q) : valuation q 43 = true ∨ valuation q 44 = true ∨ valuation q 1527 = true := counterClause973 (baseVal q)

theorem counterClause974 (q : Nat → Bool) : valuationOf q 50 = true ∨ valuationOf q 1528 = true := by
  have hs : count1528 q = (countLit q [-47]) + (countLit q [-50]) := List.countP_append (p := literal q) (l₁ := [-47]) (l₂ := [-50])
  have hm := merge_right (literal (valuationOf q) (-50)) (literal (valuationOf q) (1528)) (countLit q [-47]) (countLit q [-50]) (count1528 q) 1 (meaningNeg50 q) (meaning1528 q) hs
  change (! (valuationOf q 50)) = false ∨ valuationOf q 1528 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause974 (q : Snake 81) (h : Conditions q) : valuation q 50 = true ∨ valuation q 1528 = true := counterClause974 (baseVal q)

theorem counterClause975 (q : Nat → Bool) : valuationOf q 47 = true ∨ valuationOf q 1528 = true := by
  have hs : count1528 q = (countLit q [-47]) + (countLit q [-50]) := List.countP_append (p := literal q) (l₁ := [-47]) (l₂ := [-50])
  have hm := merge_left (literal (valuationOf q) (-47)) (literal (valuationOf q) (1528)) (countLit q [-47]) (countLit q [-50]) (count1528 q) 1 (meaningNeg47 q) (meaning1528 q) hs
  change (! (valuationOf q 47)) = false ∨ valuationOf q 1528 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause975 (q : Snake 81) (h : Conditions q) : valuation q 47 = true ∨ valuation q 1528 = true := counterClause975 (baseVal q)

theorem counterClause976 (q : Nat → Bool) : valuationOf q 47 = true ∨ valuationOf q 50 = true ∨ valuationOf q 1529 = true := by
  have hs : count1528 q = (countLit q [-47]) + (countLit q [-50]) := List.countP_append (p := literal q) (l₁ := [-47]) (l₂ := [-50])
  have hm := merge_two (literal (valuationOf q) (-47)) (literal (valuationOf q) (-50)) (literal (valuationOf q) (1529)) (countLit q [-47]) (countLit q [-50]) (count1528 q) 1 1 (meaningNeg47 q) (meaningNeg50 q) (meaning1529 q) hs
  change (! (valuationOf q 47)) = false ∨ (! (valuationOf q 50)) = false ∨ valuationOf q 1529 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause976 (q : Snake 81) (h : Conditions q) : valuation q 47 = true ∨ valuation q 50 = true ∨ valuation q 1529 = true := counterClause976 (baseVal q)

theorem counterClause977 (q : Nat → Bool) : valuationOf q 1528 = false ∨ valuationOf q 1530 = true := by
  have hs : count1530 q = (countLit q [-43, -44]) + (countLit q [-47, -50]) := List.countP_append (p := literal q) (l₁ := [-43, -44]) (l₂ := [-47, -50])
  have hm := merge_right (literal (valuationOf q) (1528)) (literal (valuationOf q) (1530)) (countLit q [-43, -44]) (countLit q [-47, -50]) (count1530 q) 1 (meaning1528 q) (meaning1530 q) hs
  change valuationOf q 1528 = false ∨ valuationOf q 1530 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause977 (q : Snake 81) (h : Conditions q) : valuation q 1528 = false ∨ valuation q 1530 = true := counterClause977 (baseVal q)

theorem counterClause978 (q : Nat → Bool) : valuationOf q 1529 = false ∨ valuationOf q 1531 = true := by
  have hs : count1530 q = (countLit q [-43, -44]) + (countLit q [-47, -50]) := List.countP_append (p := literal q) (l₁ := [-43, -44]) (l₂ := [-47, -50])
  have hm := merge_right (literal (valuationOf q) (1529)) (literal (valuationOf q) (1531)) (countLit q [-43, -44]) (countLit q [-47, -50]) (count1530 q) 2 (meaning1529 q) (meaning1531 q) hs
  change valuationOf q 1529 = false ∨ valuationOf q 1531 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause978 (q : Snake 81) (h : Conditions q) : valuation q 1529 = false ∨ valuation q 1531 = true := counterClause978 (baseVal q)

theorem counterClause979 (q : Nat → Bool) : valuationOf q 1526 = false ∨ valuationOf q 1530 = true := by
  have hs : count1530 q = (countLit q [-43, -44]) + (countLit q [-47, -50]) := List.countP_append (p := literal q) (l₁ := [-43, -44]) (l₂ := [-47, -50])
  have hm := merge_left (literal (valuationOf q) (1526)) (literal (valuationOf q) (1530)) (countLit q [-43, -44]) (countLit q [-47, -50]) (count1530 q) 1 (meaning1526 q) (meaning1530 q) hs
  change valuationOf q 1526 = false ∨ valuationOf q 1530 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause979 (q : Snake 81) (h : Conditions q) : valuation q 1526 = false ∨ valuation q 1530 = true := counterClause979 (baseVal q)

theorem counterClause980 (q : Nat → Bool) : valuationOf q 1526 = false ∨ valuationOf q 1528 = false ∨ valuationOf q 1531 = true := by
  have hs : count1530 q = (countLit q [-43, -44]) + (countLit q [-47, -50]) := List.countP_append (p := literal q) (l₁ := [-43, -44]) (l₂ := [-47, -50])
  have hm := merge_two (literal (valuationOf q) (1526)) (literal (valuationOf q) (1528)) (literal (valuationOf q) (1531)) (countLit q [-43, -44]) (countLit q [-47, -50]) (count1530 q) 1 1 (meaning1526 q) (meaning1528 q) (meaning1531 q) hs
  change valuationOf q 1526 = false ∨ valuationOf q 1528 = false ∨ valuationOf q 1531 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause980 (q : Snake 81) (h : Conditions q) : valuation q 1526 = false ∨ valuation q 1528 = false ∨ valuation q 1531 = true := counterClause980 (baseVal q)

theorem counterClause981 (q : Nat → Bool) : valuationOf q 1526 = false ∨ valuationOf q 1529 = false ∨ valuationOf q 1532 = true := by
  have hs : count1530 q = (countLit q [-43, -44]) + (countLit q [-47, -50]) := List.countP_append (p := literal q) (l₁ := [-43, -44]) (l₂ := [-47, -50])
  have hm := merge_two (literal (valuationOf q) (1526)) (literal (valuationOf q) (1529)) (literal (valuationOf q) (1532)) (countLit q [-43, -44]) (countLit q [-47, -50]) (count1530 q) 1 2 (meaning1526 q) (meaning1529 q) (meaning1532 q) hs
  change valuationOf q 1526 = false ∨ valuationOf q 1529 = false ∨ valuationOf q 1532 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause981 (q : Snake 81) (h : Conditions q) : valuation q 1526 = false ∨ valuation q 1529 = false ∨ valuation q 1532 = true := counterClause981 (baseVal q)

theorem counterClause982 (q : Nat → Bool) : valuationOf q 1527 = false ∨ valuationOf q 1531 = true := by
  have hs : count1530 q = (countLit q [-43, -44]) + (countLit q [-47, -50]) := List.countP_append (p := literal q) (l₁ := [-43, -44]) (l₂ := [-47, -50])
  have hm := merge_left (literal (valuationOf q) (1527)) (literal (valuationOf q) (1531)) (countLit q [-43, -44]) (countLit q [-47, -50]) (count1530 q) 2 (meaning1527 q) (meaning1531 q) hs
  change valuationOf q 1527 = false ∨ valuationOf q 1531 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause982 (q : Snake 81) (h : Conditions q) : valuation q 1527 = false ∨ valuation q 1531 = true := counterClause982 (baseVal q)

theorem counterClause983 (q : Nat → Bool) : valuationOf q 1527 = false ∨ valuationOf q 1528 = false ∨ valuationOf q 1532 = true := by
  have hs : count1530 q = (countLit q [-43, -44]) + (countLit q [-47, -50]) := List.countP_append (p := literal q) (l₁ := [-43, -44]) (l₂ := [-47, -50])
  have hm := merge_two (literal (valuationOf q) (1527)) (literal (valuationOf q) (1528)) (literal (valuationOf q) (1532)) (countLit q [-43, -44]) (countLit q [-47, -50]) (count1530 q) 2 1 (meaning1527 q) (meaning1528 q) (meaning1532 q) hs
  change valuationOf q 1527 = false ∨ valuationOf q 1528 = false ∨ valuationOf q 1532 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause983 (q : Snake 81) (h : Conditions q) : valuation q 1527 = false ∨ valuation q 1528 = false ∨ valuation q 1532 = true := counterClause983 (baseVal q)

theorem counterClause984 (q : Nat → Bool) : valuationOf q 1527 = false ∨ valuationOf q 1529 = false ∨ valuationOf q 1533 = true := by
  have hs : count1530 q = (countLit q [-43, -44]) + (countLit q [-47, -50]) := List.countP_append (p := literal q) (l₁ := [-43, -44]) (l₂ := [-47, -50])
  have hm := merge_two (literal (valuationOf q) (1527)) (literal (valuationOf q) (1529)) (literal (valuationOf q) (1533)) (countLit q [-43, -44]) (countLit q [-47, -50]) (count1530 q) 2 2 (meaning1527 q) (meaning1529 q) (meaning1533 q) hs
  change valuationOf q 1527 = false ∨ valuationOf q 1529 = false ∨ valuationOf q 1533 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause984 (q : Snake 81) (h : Conditions q) : valuation q 1527 = false ∨ valuation q 1529 = false ∨ valuation q 1533 = true := counterClause984 (baseVal q)

theorem counterClause985 (q : Nat → Bool) : valuationOf q 53 = true ∨ valuationOf q 1534 = true := by
  have hs : count1534 q = (countLit q [-52]) + (countLit q [-53]) := List.countP_append (p := literal q) (l₁ := [-52]) (l₂ := [-53])
  have hm := merge_right (literal (valuationOf q) (-53)) (literal (valuationOf q) (1534)) (countLit q [-52]) (countLit q [-53]) (count1534 q) 1 (meaningNeg53 q) (meaning1534 q) hs
  change (! (valuationOf q 53)) = false ∨ valuationOf q 1534 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause985 (q : Snake 81) (h : Conditions q) : valuation q 53 = true ∨ valuation q 1534 = true := counterClause985 (baseVal q)

theorem counterClause986 (q : Nat → Bool) : valuationOf q 52 = true ∨ valuationOf q 1534 = true := by
  have hs : count1534 q = (countLit q [-52]) + (countLit q [-53]) := List.countP_append (p := literal q) (l₁ := [-52]) (l₂ := [-53])
  have hm := merge_left (literal (valuationOf q) (-52)) (literal (valuationOf q) (1534)) (countLit q [-52]) (countLit q [-53]) (count1534 q) 1 (meaningNeg52 q) (meaning1534 q) hs
  change (! (valuationOf q 52)) = false ∨ valuationOf q 1534 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause986 (q : Snake 81) (h : Conditions q) : valuation q 52 = true ∨ valuation q 1534 = true := counterClause986 (baseVal q)

theorem counterClause987 (q : Nat → Bool) : valuationOf q 52 = true ∨ valuationOf q 53 = true ∨ valuationOf q 1535 = true := by
  have hs : count1534 q = (countLit q [-52]) + (countLit q [-53]) := List.countP_append (p := literal q) (l₁ := [-52]) (l₂ := [-53])
  have hm := merge_two (literal (valuationOf q) (-52)) (literal (valuationOf q) (-53)) (literal (valuationOf q) (1535)) (countLit q [-52]) (countLit q [-53]) (count1534 q) 1 1 (meaningNeg52 q) (meaningNeg53 q) (meaning1535 q) hs
  change (! (valuationOf q 52)) = false ∨ (! (valuationOf q 53)) = false ∨ valuationOf q 1535 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause987 (q : Snake 81) (h : Conditions q) : valuation q 52 = true ∨ valuation q 53 = true ∨ valuation q 1535 = true := counterClause987 (baseVal q)

theorem counterClause988 (q : Nat → Bool) : valuationOf q 55 = true ∨ valuationOf q 1536 = true := by
  have hs : count1536 q = (countLit q [-54]) + (countLit q [-55]) := List.countP_append (p := literal q) (l₁ := [-54]) (l₂ := [-55])
  have hm := merge_right (literal (valuationOf q) (-55)) (literal (valuationOf q) (1536)) (countLit q [-54]) (countLit q [-55]) (count1536 q) 1 (meaningNeg55 q) (meaning1536 q) hs
  change (! (valuationOf q 55)) = false ∨ valuationOf q 1536 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause988 (q : Snake 81) (h : Conditions q) : valuation q 55 = true ∨ valuation q 1536 = true := counterClause988 (baseVal q)

theorem counterClause989 (q : Nat → Bool) : valuationOf q 54 = true ∨ valuationOf q 1536 = true := by
  have hs : count1536 q = (countLit q [-54]) + (countLit q [-55]) := List.countP_append (p := literal q) (l₁ := [-54]) (l₂ := [-55])
  have hm := merge_left (literal (valuationOf q) (-54)) (literal (valuationOf q) (1536)) (countLit q [-54]) (countLit q [-55]) (count1536 q) 1 (meaningNeg54 q) (meaning1536 q) hs
  change (! (valuationOf q 54)) = false ∨ valuationOf q 1536 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause989 (q : Snake 81) (h : Conditions q) : valuation q 54 = true ∨ valuation q 1536 = true := counterClause989 (baseVal q)

theorem counterClause990 (q : Nat → Bool) : valuationOf q 54 = true ∨ valuationOf q 55 = true ∨ valuationOf q 1537 = true := by
  have hs : count1536 q = (countLit q [-54]) + (countLit q [-55]) := List.countP_append (p := literal q) (l₁ := [-54]) (l₂ := [-55])
  have hm := merge_two (literal (valuationOf q) (-54)) (literal (valuationOf q) (-55)) (literal (valuationOf q) (1537)) (countLit q [-54]) (countLit q [-55]) (count1536 q) 1 1 (meaningNeg54 q) (meaningNeg55 q) (meaning1537 q) hs
  change (! (valuationOf q 54)) = false ∨ (! (valuationOf q 55)) = false ∨ valuationOf q 1537 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause990 (q : Snake 81) (h : Conditions q) : valuation q 54 = true ∨ valuation q 55 = true ∨ valuation q 1537 = true := counterClause990 (baseVal q)

theorem counterClause991 (q : Nat → Bool) : valuationOf q 1536 = false ∨ valuationOf q 1538 = true := by
  have hs : count1538 q = (countLit q [-52, -53]) + (countLit q [-54, -55]) := List.countP_append (p := literal q) (l₁ := [-52, -53]) (l₂ := [-54, -55])
  have hm := merge_right (literal (valuationOf q) (1536)) (literal (valuationOf q) (1538)) (countLit q [-52, -53]) (countLit q [-54, -55]) (count1538 q) 1 (meaning1536 q) (meaning1538 q) hs
  change valuationOf q 1536 = false ∨ valuationOf q 1538 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause991 (q : Snake 81) (h : Conditions q) : valuation q 1536 = false ∨ valuation q 1538 = true := counterClause991 (baseVal q)

theorem counterClause992 (q : Nat → Bool) : valuationOf q 1537 = false ∨ valuationOf q 1539 = true := by
  have hs : count1538 q = (countLit q [-52, -53]) + (countLit q [-54, -55]) := List.countP_append (p := literal q) (l₁ := [-52, -53]) (l₂ := [-54, -55])
  have hm := merge_right (literal (valuationOf q) (1537)) (literal (valuationOf q) (1539)) (countLit q [-52, -53]) (countLit q [-54, -55]) (count1538 q) 2 (meaning1537 q) (meaning1539 q) hs
  change valuationOf q 1537 = false ∨ valuationOf q 1539 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause992 (q : Snake 81) (h : Conditions q) : valuation q 1537 = false ∨ valuation q 1539 = true := counterClause992 (baseVal q)

theorem block30 (q : Snake 81) (h : Conditions q) : B112E026.Block30 (valuation q) :=
  ⟨clause961 q h, clause962 q h, clause963 q h, clause964 q h, clause965 q h, clause966 q h, clause967 q h, clause968 q h, clause969 q h, clause970 q h, clause971 q h, clause972 q h, clause973 q h, clause974 q h, clause975 q h, clause976 q h, clause977 q h, clause978 q h, clause979 q h, clause980 q h, clause981 q h, clause982 q h, clause983 q h, clause984 q h, clause985 q h, clause986 q h, clause987 q h, clause988 q h, clause989 q h, clause990 q h, clause991 q h, clause992 q h⟩

end
end Snake9.Regrowth.E112026
