import First112Semantics
import Dfs112FirstBooleanInputs
namespace Snake9.Regrowth.First112
noncomputable section
local instance blockDec32 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause1025 (q : Snake 81) (h : Conditions q) : valuation q 1477 = false ∨ valuation q 1499 = false ∨ valuation q 1511 = true := by
  have hs : count1505 q = (countLit q [-2, -4, -6, -8, -10, -12, -13]) + (countLit q [-15, -18, -19, -21, -23, -24, -26, -27]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-2, -4, -6, -8, -10, -12, -13]) (l₂ := [-15, -18, -19, -21, -23, -24, -26, -27])
  have hm := merge_two (literal (valuation q) (1477)) (literal (valuation q) (1499)) (literal (valuation q) (1511)) (countLit q [-2, -4, -6, -8, -10, -12, -13]) (countLit q [-15, -18, -19, -21, -23, -24, -26, -27]) (count1505 q) 4 3 (meaning1477 q) (meaning1499 q) (meaning1511 q) hs
  change valuation q 1477 = false ∨ valuation q 1499 = false ∨ valuation q 1511 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1026 (q : Snake 81) (h : Conditions q) : valuation q 1477 = false ∨ valuation q 1500 = false ∨ valuation q 1512 = true := by
  have hs : count1505 q = (countLit q [-2, -4, -6, -8, -10, -12, -13]) + (countLit q [-15, -18, -19, -21, -23, -24, -26, -27]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-2, -4, -6, -8, -10, -12, -13]) (l₂ := [-15, -18, -19, -21, -23, -24, -26, -27])
  have hm := merge_two (literal (valuation q) (1477)) (literal (valuation q) (1500)) (literal (valuation q) (1512)) (countLit q [-2, -4, -6, -8, -10, -12, -13]) (countLit q [-15, -18, -19, -21, -23, -24, -26, -27]) (count1505 q) 4 4 (meaning1477 q) (meaning1500 q) (meaning1512 q) hs
  change valuation q 1477 = false ∨ valuation q 1500 = false ∨ valuation q 1512 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1027 (q : Snake 81) (h : Conditions q) : valuation q 1477 = false ∨ valuation q 1501 = false ∨ valuation q 1513 = true := by
  have hs : count1505 q = (countLit q [-2, -4, -6, -8, -10, -12, -13]) + (countLit q [-15, -18, -19, -21, -23, -24, -26, -27]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-2, -4, -6, -8, -10, -12, -13]) (l₂ := [-15, -18, -19, -21, -23, -24, -26, -27])
  have hm := merge_two (literal (valuation q) (1477)) (literal (valuation q) (1501)) (literal (valuation q) (1513)) (countLit q [-2, -4, -6, -8, -10, -12, -13]) (countLit q [-15, -18, -19, -21, -23, -24, -26, -27]) (count1505 q) 4 5 (meaning1477 q) (meaning1501 q) (meaning1513 q) hs
  change valuation q 1477 = false ∨ valuation q 1501 = false ∨ valuation q 1513 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1028 (q : Snake 81) (h : Conditions q) : valuation q 1478 = false ∨ valuation q 1497 = false ∨ valuation q 1510 = true := by
  have hs : count1505 q = (countLit q [-2, -4, -6, -8, -10, -12, -13]) + (countLit q [-15, -18, -19, -21, -23, -24, -26, -27]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-2, -4, -6, -8, -10, -12, -13]) (l₂ := [-15, -18, -19, -21, -23, -24, -26, -27])
  have hm := merge_two (literal (valuation q) (1478)) (literal (valuation q) (1497)) (literal (valuation q) (1510)) (countLit q [-2, -4, -6, -8, -10, -12, -13]) (countLit q [-15, -18, -19, -21, -23, -24, -26, -27]) (count1505 q) 5 1 (meaning1478 q) (meaning1497 q) (meaning1510 q) hs
  change valuation q 1478 = false ∨ valuation q 1497 = false ∨ valuation q 1510 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1029 (q : Snake 81) (h : Conditions q) : valuation q 1478 = false ∨ valuation q 1498 = false ∨ valuation q 1511 = true := by
  have hs : count1505 q = (countLit q [-2, -4, -6, -8, -10, -12, -13]) + (countLit q [-15, -18, -19, -21, -23, -24, -26, -27]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-2, -4, -6, -8, -10, -12, -13]) (l₂ := [-15, -18, -19, -21, -23, -24, -26, -27])
  have hm := merge_two (literal (valuation q) (1478)) (literal (valuation q) (1498)) (literal (valuation q) (1511)) (countLit q [-2, -4, -6, -8, -10, -12, -13]) (countLit q [-15, -18, -19, -21, -23, -24, -26, -27]) (count1505 q) 5 2 (meaning1478 q) (meaning1498 q) (meaning1511 q) hs
  change valuation q 1478 = false ∨ valuation q 1498 = false ∨ valuation q 1511 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1030 (q : Snake 81) (h : Conditions q) : valuation q 1478 = false ∨ valuation q 1499 = false ∨ valuation q 1512 = true := by
  have hs : count1505 q = (countLit q [-2, -4, -6, -8, -10, -12, -13]) + (countLit q [-15, -18, -19, -21, -23, -24, -26, -27]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-2, -4, -6, -8, -10, -12, -13]) (l₂ := [-15, -18, -19, -21, -23, -24, -26, -27])
  have hm := merge_two (literal (valuation q) (1478)) (literal (valuation q) (1499)) (literal (valuation q) (1512)) (countLit q [-2, -4, -6, -8, -10, -12, -13]) (countLit q [-15, -18, -19, -21, -23, -24, -26, -27]) (count1505 q) 5 3 (meaning1478 q) (meaning1499 q) (meaning1512 q) hs
  change valuation q 1478 = false ∨ valuation q 1499 = false ∨ valuation q 1512 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1031 (q : Snake 81) (h : Conditions q) : valuation q 1478 = false ∨ valuation q 1500 = false ∨ valuation q 1513 = true := by
  have hs : count1505 q = (countLit q [-2, -4, -6, -8, -10, -12, -13]) + (countLit q [-15, -18, -19, -21, -23, -24, -26, -27]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-2, -4, -6, -8, -10, -12, -13]) (l₂ := [-15, -18, -19, -21, -23, -24, -26, -27])
  have hm := merge_two (literal (valuation q) (1478)) (literal (valuation q) (1500)) (literal (valuation q) (1513)) (countLit q [-2, -4, -6, -8, -10, -12, -13]) (countLit q [-15, -18, -19, -21, -23, -24, -26, -27]) (count1505 q) 5 4 (meaning1478 q) (meaning1500 q) (meaning1513 q) hs
  change valuation q 1478 = false ∨ valuation q 1500 = false ∨ valuation q 1513 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1032 (q : Snake 81) (h : Conditions q) : valuation q 1479 = false ∨ valuation q 1497 = false ∨ valuation q 1511 = true := by
  have hs : count1505 q = (countLit q [-2, -4, -6, -8, -10, -12, -13]) + (countLit q [-15, -18, -19, -21, -23, -24, -26, -27]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-2, -4, -6, -8, -10, -12, -13]) (l₂ := [-15, -18, -19, -21, -23, -24, -26, -27])
  have hm := merge_two (literal (valuation q) (1479)) (literal (valuation q) (1497)) (literal (valuation q) (1511)) (countLit q [-2, -4, -6, -8, -10, -12, -13]) (countLit q [-15, -18, -19, -21, -23, -24, -26, -27]) (count1505 q) 6 1 (meaning1479 q) (meaning1497 q) (meaning1511 q) hs
  change valuation q 1479 = false ∨ valuation q 1497 = false ∨ valuation q 1511 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1033 (q : Snake 81) (h : Conditions q) : valuation q 33 = true ∨ valuation q 1520 = true := by
  have hs : count1520 q = (countLit q [-31]) + (countLit q [-33]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-31]) (l₂ := [-33])
  have hm := merge_right (literal (valuation q) (-33)) (literal (valuation q) (1520)) (countLit q [-31]) (countLit q [-33]) (count1520 q) 1 (meaningNeg33 q) (meaning1520 q) hs
  change (! (valuation q 33)) = false ∨ valuation q 1520 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1034 (q : Snake 81) (h : Conditions q) : valuation q 31 = true ∨ valuation q 1520 = true := by
  have hs : count1520 q = (countLit q [-31]) + (countLit q [-33]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-31]) (l₂ := [-33])
  have hm := merge_left (literal (valuation q) (-31)) (literal (valuation q) (1520)) (countLit q [-31]) (countLit q [-33]) (count1520 q) 1 (meaningNeg31 q) (meaning1520 q) hs
  change (! (valuation q 31)) = false ∨ valuation q 1520 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1035 (q : Snake 81) (h : Conditions q) : valuation q 31 = true ∨ valuation q 33 = true ∨ valuation q 1521 = true := by
  have hs : count1520 q = (countLit q [-31]) + (countLit q [-33]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-31]) (l₂ := [-33])
  have hm := merge_two (literal (valuation q) (-31)) (literal (valuation q) (-33)) (literal (valuation q) (1521)) (countLit q [-31]) (countLit q [-33]) (count1520 q) 1 1 (meaningNeg31 q) (meaningNeg33 q) (meaning1521 q) hs
  change (! (valuation q 31)) = false ∨ (! (valuation q 33)) = false ∨ valuation q 1521 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1036 (q : Snake 81) (h : Conditions q) : valuation q 35 = true ∨ valuation q 1522 = true := by
  have hs : count1522 q = (countLit q [-34]) + (countLit q [-35]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-34]) (l₂ := [-35])
  have hm := merge_right (literal (valuation q) (-35)) (literal (valuation q) (1522)) (countLit q [-34]) (countLit q [-35]) (count1522 q) 1 (meaningNeg35 q) (meaning1522 q) hs
  change (! (valuation q 35)) = false ∨ valuation q 1522 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1037 (q : Snake 81) (h : Conditions q) : valuation q 34 = true ∨ valuation q 1522 = true := by
  have hs : count1522 q = (countLit q [-34]) + (countLit q [-35]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-34]) (l₂ := [-35])
  have hm := merge_left (literal (valuation q) (-34)) (literal (valuation q) (1522)) (countLit q [-34]) (countLit q [-35]) (count1522 q) 1 (meaningNeg34 q) (meaning1522 q) hs
  change (! (valuation q 34)) = false ∨ valuation q 1522 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1038 (q : Snake 81) (h : Conditions q) : valuation q 34 = true ∨ valuation q 35 = true ∨ valuation q 1523 = true := by
  have hs : count1522 q = (countLit q [-34]) + (countLit q [-35]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-34]) (l₂ := [-35])
  have hm := merge_two (literal (valuation q) (-34)) (literal (valuation q) (-35)) (literal (valuation q) (1523)) (countLit q [-34]) (countLit q [-35]) (count1522 q) 1 1 (meaningNeg34 q) (meaningNeg35 q) (meaning1523 q) hs
  change (! (valuation q 34)) = false ∨ (! (valuation q 35)) = false ∨ valuation q 1523 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1039 (q : Snake 81) (h : Conditions q) : valuation q 1522 = false ∨ valuation q 1524 = true := by
  have hs : count1524 q = (countLit q [-31, -33]) + (countLit q [-34, -35]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-31, -33]) (l₂ := [-34, -35])
  have hm := merge_right (literal (valuation q) (1522)) (literal (valuation q) (1524)) (countLit q [-31, -33]) (countLit q [-34, -35]) (count1524 q) 1 (meaning1522 q) (meaning1524 q) hs
  change valuation q 1522 = false ∨ valuation q 1524 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1040 (q : Snake 81) (h : Conditions q) : valuation q 1523 = false ∨ valuation q 1525 = true := by
  have hs : count1524 q = (countLit q [-31, -33]) + (countLit q [-34, -35]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-31, -33]) (l₂ := [-34, -35])
  have hm := merge_right (literal (valuation q) (1523)) (literal (valuation q) (1525)) (countLit q [-31, -33]) (countLit q [-34, -35]) (count1524 q) 2 (meaning1523 q) (meaning1525 q) hs
  change valuation q 1523 = false ∨ valuation q 1525 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1041 (q : Snake 81) (h : Conditions q) : valuation q 1520 = false ∨ valuation q 1524 = true := by
  have hs : count1524 q = (countLit q [-31, -33]) + (countLit q [-34, -35]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-31, -33]) (l₂ := [-34, -35])
  have hm := merge_left (literal (valuation q) (1520)) (literal (valuation q) (1524)) (countLit q [-31, -33]) (countLit q [-34, -35]) (count1524 q) 1 (meaning1520 q) (meaning1524 q) hs
  change valuation q 1520 = false ∨ valuation q 1524 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1042 (q : Snake 81) (h : Conditions q) : valuation q 1520 = false ∨ valuation q 1522 = false ∨ valuation q 1525 = true := by
  have hs : count1524 q = (countLit q [-31, -33]) + (countLit q [-34, -35]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-31, -33]) (l₂ := [-34, -35])
  have hm := merge_two (literal (valuation q) (1520)) (literal (valuation q) (1522)) (literal (valuation q) (1525)) (countLit q [-31, -33]) (countLit q [-34, -35]) (count1524 q) 1 1 (meaning1520 q) (meaning1522 q) (meaning1525 q) hs
  change valuation q 1520 = false ∨ valuation q 1522 = false ∨ valuation q 1525 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1043 (q : Snake 81) (h : Conditions q) : valuation q 1521 = false ∨ valuation q 1525 = true := by
  have hs : count1524 q = (countLit q [-31, -33]) + (countLit q [-34, -35]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-31, -33]) (l₂ := [-34, -35])
  have hm := merge_left (literal (valuation q) (1521)) (literal (valuation q) (1525)) (countLit q [-31, -33]) (countLit q [-34, -35]) (count1524 q) 2 (meaning1521 q) (meaning1525 q) hs
  change valuation q 1521 = false ∨ valuation q 1525 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1044 (q : Snake 81) (h : Conditions q) : valuation q 41 = true ∨ valuation q 1528 = true := by
  have hs : count1528 q = (countLit q [-39]) + (countLit q [-41]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-39]) (l₂ := [-41])
  have hm := merge_right (literal (valuation q) (-41)) (literal (valuation q) (1528)) (countLit q [-39]) (countLit q [-41]) (count1528 q) 1 (meaningNeg41 q) (meaning1528 q) hs
  change (! (valuation q 41)) = false ∨ valuation q 1528 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1045 (q : Snake 81) (h : Conditions q) : valuation q 39 = true ∨ valuation q 1528 = true := by
  have hs : count1528 q = (countLit q [-39]) + (countLit q [-41]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-39]) (l₂ := [-41])
  have hm := merge_left (literal (valuation q) (-39)) (literal (valuation q) (1528)) (countLit q [-39]) (countLit q [-41]) (count1528 q) 1 (meaningNeg39 q) (meaning1528 q) hs
  change (! (valuation q 39)) = false ∨ valuation q 1528 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1046 (q : Snake 81) (h : Conditions q) : valuation q 39 = true ∨ valuation q 41 = true ∨ valuation q 1529 = true := by
  have hs : count1528 q = (countLit q [-39]) + (countLit q [-41]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-39]) (l₂ := [-41])
  have hm := merge_two (literal (valuation q) (-39)) (literal (valuation q) (-41)) (literal (valuation q) (1529)) (countLit q [-39]) (countLit q [-41]) (count1528 q) 1 1 (meaningNeg39 q) (meaningNeg41 q) (meaning1529 q) hs
  change (! (valuation q 39)) = false ∨ (! (valuation q 41)) = false ∨ valuation q 1529 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1047 (q : Snake 81) (h : Conditions q) : valuation q 43 = true ∨ valuation q 1530 = true := by
  have hs : count1530 q = (countLit q [-42]) + (countLit q [-43]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-42]) (l₂ := [-43])
  have hm := merge_right (literal (valuation q) (-43)) (literal (valuation q) (1530)) (countLit q [-42]) (countLit q [-43]) (count1530 q) 1 (meaningNeg43 q) (meaning1530 q) hs
  change (! (valuation q 43)) = false ∨ valuation q 1530 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1048 (q : Snake 81) (h : Conditions q) : valuation q 42 = true ∨ valuation q 1530 = true := by
  have hs : count1530 q = (countLit q [-42]) + (countLit q [-43]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-42]) (l₂ := [-43])
  have hm := merge_left (literal (valuation q) (-42)) (literal (valuation q) (1530)) (countLit q [-42]) (countLit q [-43]) (count1530 q) 1 (meaningNeg42 q) (meaning1530 q) hs
  change (! (valuation q 42)) = false ∨ valuation q 1530 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1049 (q : Snake 81) (h : Conditions q) : valuation q 42 = true ∨ valuation q 43 = true ∨ valuation q 1531 = true := by
  have hs : count1530 q = (countLit q [-42]) + (countLit q [-43]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-42]) (l₂ := [-43])
  have hm := merge_two (literal (valuation q) (-42)) (literal (valuation q) (-43)) (literal (valuation q) (1531)) (countLit q [-42]) (countLit q [-43]) (count1530 q) 1 1 (meaningNeg42 q) (meaningNeg43 q) (meaning1531 q) hs
  change (! (valuation q 42)) = false ∨ (! (valuation q 43)) = false ∨ valuation q 1531 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1050 (q : Snake 81) (h : Conditions q) : valuation q 1530 = false ∨ valuation q 1532 = true := by
  have hs : count1532 q = (countLit q [-39, -41]) + (countLit q [-42, -43]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-39, -41]) (l₂ := [-42, -43])
  have hm := merge_right (literal (valuation q) (1530)) (literal (valuation q) (1532)) (countLit q [-39, -41]) (countLit q [-42, -43]) (count1532 q) 1 (meaning1530 q) (meaning1532 q) hs
  change valuation q 1530 = false ∨ valuation q 1532 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1051 (q : Snake 81) (h : Conditions q) : valuation q 1531 = false ∨ valuation q 1533 = true := by
  have hs : count1532 q = (countLit q [-39, -41]) + (countLit q [-42, -43]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-39, -41]) (l₂ := [-42, -43])
  have hm := merge_right (literal (valuation q) (1531)) (literal (valuation q) (1533)) (countLit q [-39, -41]) (countLit q [-42, -43]) (count1532 q) 2 (meaning1531 q) (meaning1533 q) hs
  change valuation q 1531 = false ∨ valuation q 1533 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1052 (q : Snake 81) (h : Conditions q) : valuation q 1528 = false ∨ valuation q 1532 = true := by
  have hs : count1532 q = (countLit q [-39, -41]) + (countLit q [-42, -43]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-39, -41]) (l₂ := [-42, -43])
  have hm := merge_left (literal (valuation q) (1528)) (literal (valuation q) (1532)) (countLit q [-39, -41]) (countLit q [-42, -43]) (count1532 q) 1 (meaning1528 q) (meaning1532 q) hs
  change valuation q 1528 = false ∨ valuation q 1532 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1053 (q : Snake 81) (h : Conditions q) : valuation q 1528 = false ∨ valuation q 1530 = false ∨ valuation q 1533 = true := by
  have hs : count1532 q = (countLit q [-39, -41]) + (countLit q [-42, -43]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-39, -41]) (l₂ := [-42, -43])
  have hm := merge_two (literal (valuation q) (1528)) (literal (valuation q) (1530)) (literal (valuation q) (1533)) (countLit q [-39, -41]) (countLit q [-42, -43]) (count1532 q) 1 1 (meaning1528 q) (meaning1530 q) (meaning1533 q) hs
  change valuation q 1528 = false ∨ valuation q 1530 = false ∨ valuation q 1533 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1054 (q : Snake 81) (h : Conditions q) : valuation q 1528 = false ∨ valuation q 1531 = false ∨ valuation q 1534 = true := by
  have hs : count1532 q = (countLit q [-39, -41]) + (countLit q [-42, -43]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-39, -41]) (l₂ := [-42, -43])
  have hm := merge_two (literal (valuation q) (1528)) (literal (valuation q) (1531)) (literal (valuation q) (1534)) (countLit q [-39, -41]) (countLit q [-42, -43]) (count1532 q) 1 2 (meaning1528 q) (meaning1531 q) (meaning1534 q) hs
  change valuation q 1528 = false ∨ valuation q 1531 = false ∨ valuation q 1534 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1055 (q : Snake 81) (h : Conditions q) : valuation q 1529 = false ∨ valuation q 1533 = true := by
  have hs : count1532 q = (countLit q [-39, -41]) + (countLit q [-42, -43]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-39, -41]) (l₂ := [-42, -43])
  have hm := merge_left (literal (valuation q) (1529)) (literal (valuation q) (1533)) (countLit q [-39, -41]) (countLit q [-42, -43]) (count1532 q) 2 (meaning1529 q) (meaning1533 q) hs
  change valuation q 1529 = false ∨ valuation q 1533 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1056 (q : Snake 81) (h : Conditions q) : valuation q 1529 = false ∨ valuation q 1530 = false ∨ valuation q 1534 = true := by
  have hs : count1532 q = (countLit q [-39, -41]) + (countLit q [-42, -43]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-39, -41]) (l₂ := [-42, -43])
  have hm := merge_two (literal (valuation q) (1529)) (literal (valuation q) (1530)) (literal (valuation q) (1534)) (countLit q [-39, -41]) (countLit q [-42, -43]) (count1532 q) 2 1 (meaning1529 q) (meaning1530 q) (meaning1534 q) hs
  change valuation q 1529 = false ∨ valuation q 1530 = false ∨ valuation q 1534 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem block32 (q : Snake 81) (h : Conditions q) : Dfs112FirstBoolean.Block32 (valuation q) :=
  ⟨clause1025 q h, clause1026 q h, clause1027 q h, clause1028 q h, clause1029 q h, clause1030 q h, clause1031 q h, clause1032 q h, clause1033 q h, clause1034 q h, clause1035 q h, clause1036 q h, clause1037 q h, clause1038 q h, clause1039 q h, clause1040 q h, clause1041 q h, clause1042 q h, clause1043 q h, clause1044 q h, clause1045 q h, clause1046 q h, clause1047 q h, clause1048 q h, clause1049 q h, clause1050 q h, clause1051 q h, clause1052 q h, clause1053 q h, clause1054 q h, clause1055 q h, clause1056 q h⟩

end
end Snake9.Regrowth.First112
