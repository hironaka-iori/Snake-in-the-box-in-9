import First112Semantics
import Dfs112FirstBooleanInputs
namespace Snake9.Regrowth.First112
noncomputable section
local instance blockDec31 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause993 (q : Snake 81) (h : Conditions q) : valuation q 1490 = false ∨ valuation q 1491 = false ∨ valuation q 1495 = true := by
  have hs : count1493 q = (countLit q [-23, -24]) + (countLit q [-26, -27]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-23, -24]) (l₂ := [-26, -27])
  have hm := merge_two (literal (valuation q) (1490)) (literal (valuation q) (1491)) (literal (valuation q) (1495)) (countLit q [-23, -24]) (countLit q [-26, -27]) (count1493 q) 2 1 (meaning1490 q) (meaning1491 q) (meaning1495 q) hs
  change valuation q 1490 = false ∨ valuation q 1491 = false ∨ valuation q 1495 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause994 (q : Snake 81) (h : Conditions q) : valuation q 1493 = false ∨ valuation q 1497 = true := by
  have hs : count1497 q = (countLit q [-15, -18, -19, -21]) + (countLit q [-23, -24, -26, -27]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-15, -18, -19, -21]) (l₂ := [-23, -24, -26, -27])
  have hm := merge_right (literal (valuation q) (1493)) (literal (valuation q) (1497)) (countLit q [-15, -18, -19, -21]) (countLit q [-23, -24, -26, -27]) (count1497 q) 1 (meaning1493 q) (meaning1497 q) hs
  change valuation q 1493 = false ∨ valuation q 1497 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause995 (q : Snake 81) (h : Conditions q) : valuation q 1494 = false ∨ valuation q 1498 = true := by
  have hs : count1497 q = (countLit q [-15, -18, -19, -21]) + (countLit q [-23, -24, -26, -27]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-15, -18, -19, -21]) (l₂ := [-23, -24, -26, -27])
  have hm := merge_right (literal (valuation q) (1494)) (literal (valuation q) (1498)) (countLit q [-15, -18, -19, -21]) (countLit q [-23, -24, -26, -27]) (count1497 q) 2 (meaning1494 q) (meaning1498 q) hs
  change valuation q 1494 = false ∨ valuation q 1498 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause996 (q : Snake 81) (h : Conditions q) : valuation q 1495 = false ∨ valuation q 1499 = true := by
  have hs : count1497 q = (countLit q [-15, -18, -19, -21]) + (countLit q [-23, -24, -26, -27]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-15, -18, -19, -21]) (l₂ := [-23, -24, -26, -27])
  have hm := merge_right (literal (valuation q) (1495)) (literal (valuation q) (1499)) (countLit q [-15, -18, -19, -21]) (countLit q [-23, -24, -26, -27]) (count1497 q) 3 (meaning1495 q) (meaning1499 q) hs
  change valuation q 1495 = false ∨ valuation q 1499 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause997 (q : Snake 81) (h : Conditions q) : valuation q 1485 = false ∨ valuation q 1497 = true := by
  have hs : count1497 q = (countLit q [-15, -18, -19, -21]) + (countLit q [-23, -24, -26, -27]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-15, -18, -19, -21]) (l₂ := [-23, -24, -26, -27])
  have hm := merge_left (literal (valuation q) (1485)) (literal (valuation q) (1497)) (countLit q [-15, -18, -19, -21]) (countLit q [-23, -24, -26, -27]) (count1497 q) 1 (meaning1485 q) (meaning1497 q) hs
  change valuation q 1485 = false ∨ valuation q 1497 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause998 (q : Snake 81) (h : Conditions q) : valuation q 1485 = false ∨ valuation q 1493 = false ∨ valuation q 1498 = true := by
  have hs : count1497 q = (countLit q [-15, -18, -19, -21]) + (countLit q [-23, -24, -26, -27]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-15, -18, -19, -21]) (l₂ := [-23, -24, -26, -27])
  have hm := merge_two (literal (valuation q) (1485)) (literal (valuation q) (1493)) (literal (valuation q) (1498)) (countLit q [-15, -18, -19, -21]) (countLit q [-23, -24, -26, -27]) (count1497 q) 1 1 (meaning1485 q) (meaning1493 q) (meaning1498 q) hs
  change valuation q 1485 = false ∨ valuation q 1493 = false ∨ valuation q 1498 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause999 (q : Snake 81) (h : Conditions q) : valuation q 1485 = false ∨ valuation q 1494 = false ∨ valuation q 1499 = true := by
  have hs : count1497 q = (countLit q [-15, -18, -19, -21]) + (countLit q [-23, -24, -26, -27]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-15, -18, -19, -21]) (l₂ := [-23, -24, -26, -27])
  have hm := merge_two (literal (valuation q) (1485)) (literal (valuation q) (1494)) (literal (valuation q) (1499)) (countLit q [-15, -18, -19, -21]) (countLit q [-23, -24, -26, -27]) (count1497 q) 1 2 (meaning1485 q) (meaning1494 q) (meaning1499 q) hs
  change valuation q 1485 = false ∨ valuation q 1494 = false ∨ valuation q 1499 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1000 (q : Snake 81) (h : Conditions q) : valuation q 1485 = false ∨ valuation q 1495 = false ∨ valuation q 1500 = true := by
  have hs : count1497 q = (countLit q [-15, -18, -19, -21]) + (countLit q [-23, -24, -26, -27]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-15, -18, -19, -21]) (l₂ := [-23, -24, -26, -27])
  have hm := merge_two (literal (valuation q) (1485)) (literal (valuation q) (1495)) (literal (valuation q) (1500)) (countLit q [-15, -18, -19, -21]) (countLit q [-23, -24, -26, -27]) (count1497 q) 1 3 (meaning1485 q) (meaning1495 q) (meaning1500 q) hs
  change valuation q 1485 = false ∨ valuation q 1495 = false ∨ valuation q 1500 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1001 (q : Snake 81) (h : Conditions q) : valuation q 1486 = false ∨ valuation q 1493 = false ∨ valuation q 1499 = true := by
  have hs : count1497 q = (countLit q [-15, -18, -19, -21]) + (countLit q [-23, -24, -26, -27]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-15, -18, -19, -21]) (l₂ := [-23, -24, -26, -27])
  have hm := merge_two (literal (valuation q) (1486)) (literal (valuation q) (1493)) (literal (valuation q) (1499)) (countLit q [-15, -18, -19, -21]) (countLit q [-23, -24, -26, -27]) (count1497 q) 2 1 (meaning1486 q) (meaning1493 q) (meaning1499 q) hs
  change valuation q 1486 = false ∨ valuation q 1493 = false ∨ valuation q 1499 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1002 (q : Snake 81) (h : Conditions q) : valuation q 1486 = false ∨ valuation q 1494 = false ∨ valuation q 1500 = true := by
  have hs : count1497 q = (countLit q [-15, -18, -19, -21]) + (countLit q [-23, -24, -26, -27]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-15, -18, -19, -21]) (l₂ := [-23, -24, -26, -27])
  have hm := merge_two (literal (valuation q) (1486)) (literal (valuation q) (1494)) (literal (valuation q) (1500)) (countLit q [-15, -18, -19, -21]) (countLit q [-23, -24, -26, -27]) (count1497 q) 2 2 (meaning1486 q) (meaning1494 q) (meaning1500 q) hs
  change valuation q 1486 = false ∨ valuation q 1494 = false ∨ valuation q 1500 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1003 (q : Snake 81) (h : Conditions q) : valuation q 1486 = false ∨ valuation q 1495 = false ∨ valuation q 1501 = true := by
  have hs : count1497 q = (countLit q [-15, -18, -19, -21]) + (countLit q [-23, -24, -26, -27]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-15, -18, -19, -21]) (l₂ := [-23, -24, -26, -27])
  have hm := merge_two (literal (valuation q) (1486)) (literal (valuation q) (1495)) (literal (valuation q) (1501)) (countLit q [-15, -18, -19, -21]) (countLit q [-23, -24, -26, -27]) (count1497 q) 2 3 (meaning1486 q) (meaning1495 q) (meaning1501 q) hs
  change valuation q 1486 = false ∨ valuation q 1495 = false ∨ valuation q 1501 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1004 (q : Snake 81) (h : Conditions q) : valuation q 1487 = false ∨ valuation q 1499 = true := by
  have hs : count1497 q = (countLit q [-15, -18, -19, -21]) + (countLit q [-23, -24, -26, -27]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-15, -18, -19, -21]) (l₂ := [-23, -24, -26, -27])
  have hm := merge_left (literal (valuation q) (1487)) (literal (valuation q) (1499)) (countLit q [-15, -18, -19, -21]) (countLit q [-23, -24, -26, -27]) (count1497 q) 3 (meaning1487 q) (meaning1499 q) hs
  change valuation q 1487 = false ∨ valuation q 1499 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1005 (q : Snake 81) (h : Conditions q) : valuation q 1487 = false ∨ valuation q 1493 = false ∨ valuation q 1500 = true := by
  have hs : count1497 q = (countLit q [-15, -18, -19, -21]) + (countLit q [-23, -24, -26, -27]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-15, -18, -19, -21]) (l₂ := [-23, -24, -26, -27])
  have hm := merge_two (literal (valuation q) (1487)) (literal (valuation q) (1493)) (literal (valuation q) (1500)) (countLit q [-15, -18, -19, -21]) (countLit q [-23, -24, -26, -27]) (count1497 q) 3 1 (meaning1487 q) (meaning1493 q) (meaning1500 q) hs
  change valuation q 1487 = false ∨ valuation q 1493 = false ∨ valuation q 1500 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1006 (q : Snake 81) (h : Conditions q) : valuation q 1487 = false ∨ valuation q 1494 = false ∨ valuation q 1501 = true := by
  have hs : count1497 q = (countLit q [-15, -18, -19, -21]) + (countLit q [-23, -24, -26, -27]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-15, -18, -19, -21]) (l₂ := [-23, -24, -26, -27])
  have hm := merge_two (literal (valuation q) (1487)) (literal (valuation q) (1494)) (literal (valuation q) (1501)) (countLit q [-15, -18, -19, -21]) (countLit q [-23, -24, -26, -27]) (count1497 q) 3 2 (meaning1487 q) (meaning1494 q) (meaning1501 q) hs
  change valuation q 1487 = false ∨ valuation q 1494 = false ∨ valuation q 1501 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1007 (q : Snake 81) (h : Conditions q) : valuation q 1487 = false ∨ valuation q 1495 = false ∨ valuation q 1502 = true := by
  have hs : count1497 q = (countLit q [-15, -18, -19, -21]) + (countLit q [-23, -24, -26, -27]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-15, -18, -19, -21]) (l₂ := [-23, -24, -26, -27])
  have hm := merge_two (literal (valuation q) (1487)) (literal (valuation q) (1495)) (literal (valuation q) (1502)) (countLit q [-15, -18, -19, -21]) (countLit q [-23, -24, -26, -27]) (count1497 q) 3 3 (meaning1487 q) (meaning1495 q) (meaning1502 q) hs
  change valuation q 1487 = false ∨ valuation q 1495 = false ∨ valuation q 1502 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1008 (q : Snake 81) (h : Conditions q) : valuation q 1488 = false ∨ valuation q 1493 = false ∨ valuation q 1501 = true := by
  have hs : count1497 q = (countLit q [-15, -18, -19, -21]) + (countLit q [-23, -24, -26, -27]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-15, -18, -19, -21]) (l₂ := [-23, -24, -26, -27])
  have hm := merge_two (literal (valuation q) (1488)) (literal (valuation q) (1493)) (literal (valuation q) (1501)) (countLit q [-15, -18, -19, -21]) (countLit q [-23, -24, -26, -27]) (count1497 q) 4 1 (meaning1488 q) (meaning1493 q) (meaning1501 q) hs
  change valuation q 1488 = false ∨ valuation q 1493 = false ∨ valuation q 1501 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1009 (q : Snake 81) (h : Conditions q) : valuation q 1474 = false ∨ valuation q 1499 = false ∨ valuation q 1508 = true := by
  have hs : count1505 q = (countLit q [-2, -4, -6, -8, -10, -12, -13]) + (countLit q [-15, -18, -19, -21, -23, -24, -26, -27]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-2, -4, -6, -8, -10, -12, -13]) (l₂ := [-15, -18, -19, -21, -23, -24, -26, -27])
  have hm := merge_two (literal (valuation q) (1474)) (literal (valuation q) (1499)) (literal (valuation q) (1508)) (countLit q [-2, -4, -6, -8, -10, -12, -13]) (countLit q [-15, -18, -19, -21, -23, -24, -26, -27]) (count1505 q) 1 3 (meaning1474 q) (meaning1499 q) (meaning1508 q) hs
  change valuation q 1474 = false ∨ valuation q 1499 = false ∨ valuation q 1508 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1010 (q : Snake 81) (h : Conditions q) : valuation q 1474 = false ∨ valuation q 1500 = false ∨ valuation q 1509 = true := by
  have hs : count1505 q = (countLit q [-2, -4, -6, -8, -10, -12, -13]) + (countLit q [-15, -18, -19, -21, -23, -24, -26, -27]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-2, -4, -6, -8, -10, -12, -13]) (l₂ := [-15, -18, -19, -21, -23, -24, -26, -27])
  have hm := merge_two (literal (valuation q) (1474)) (literal (valuation q) (1500)) (literal (valuation q) (1509)) (countLit q [-2, -4, -6, -8, -10, -12, -13]) (countLit q [-15, -18, -19, -21, -23, -24, -26, -27]) (count1505 q) 1 4 (meaning1474 q) (meaning1500 q) (meaning1509 q) hs
  change valuation q 1474 = false ∨ valuation q 1500 = false ∨ valuation q 1509 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1011 (q : Snake 81) (h : Conditions q) : valuation q 1475 = false ∨ valuation q 1497 = false ∨ valuation q 1507 = true := by
  have hs : count1505 q = (countLit q [-2, -4, -6, -8, -10, -12, -13]) + (countLit q [-15, -18, -19, -21, -23, -24, -26, -27]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-2, -4, -6, -8, -10, -12, -13]) (l₂ := [-15, -18, -19, -21, -23, -24, -26, -27])
  have hm := merge_two (literal (valuation q) (1475)) (literal (valuation q) (1497)) (literal (valuation q) (1507)) (countLit q [-2, -4, -6, -8, -10, -12, -13]) (countLit q [-15, -18, -19, -21, -23, -24, -26, -27]) (count1505 q) 2 1 (meaning1475 q) (meaning1497 q) (meaning1507 q) hs
  change valuation q 1475 = false ∨ valuation q 1497 = false ∨ valuation q 1507 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1012 (q : Snake 81) (h : Conditions q) : valuation q 1475 = false ∨ valuation q 1498 = false ∨ valuation q 1508 = true := by
  have hs : count1505 q = (countLit q [-2, -4, -6, -8, -10, -12, -13]) + (countLit q [-15, -18, -19, -21, -23, -24, -26, -27]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-2, -4, -6, -8, -10, -12, -13]) (l₂ := [-15, -18, -19, -21, -23, -24, -26, -27])
  have hm := merge_two (literal (valuation q) (1475)) (literal (valuation q) (1498)) (literal (valuation q) (1508)) (countLit q [-2, -4, -6, -8, -10, -12, -13]) (countLit q [-15, -18, -19, -21, -23, -24, -26, -27]) (count1505 q) 2 2 (meaning1475 q) (meaning1498 q) (meaning1508 q) hs
  change valuation q 1475 = false ∨ valuation q 1498 = false ∨ valuation q 1508 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1013 (q : Snake 81) (h : Conditions q) : valuation q 1475 = false ∨ valuation q 1499 = false ∨ valuation q 1509 = true := by
  have hs : count1505 q = (countLit q [-2, -4, -6, -8, -10, -12, -13]) + (countLit q [-15, -18, -19, -21, -23, -24, -26, -27]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-2, -4, -6, -8, -10, -12, -13]) (l₂ := [-15, -18, -19, -21, -23, -24, -26, -27])
  have hm := merge_two (literal (valuation q) (1475)) (literal (valuation q) (1499)) (literal (valuation q) (1509)) (countLit q [-2, -4, -6, -8, -10, -12, -13]) (countLit q [-15, -18, -19, -21, -23, -24, -26, -27]) (count1505 q) 2 3 (meaning1475 q) (meaning1499 q) (meaning1509 q) hs
  change valuation q 1475 = false ∨ valuation q 1499 = false ∨ valuation q 1509 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1014 (q : Snake 81) (h : Conditions q) : valuation q 1475 = false ∨ valuation q 1500 = false ∨ valuation q 1510 = true := by
  have hs : count1505 q = (countLit q [-2, -4, -6, -8, -10, -12, -13]) + (countLit q [-15, -18, -19, -21, -23, -24, -26, -27]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-2, -4, -6, -8, -10, -12, -13]) (l₂ := [-15, -18, -19, -21, -23, -24, -26, -27])
  have hm := merge_two (literal (valuation q) (1475)) (literal (valuation q) (1500)) (literal (valuation q) (1510)) (countLit q [-2, -4, -6, -8, -10, -12, -13]) (countLit q [-15, -18, -19, -21, -23, -24, -26, -27]) (count1505 q) 2 4 (meaning1475 q) (meaning1500 q) (meaning1510 q) hs
  change valuation q 1475 = false ∨ valuation q 1500 = false ∨ valuation q 1510 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1015 (q : Snake 81) (h : Conditions q) : valuation q 1475 = false ∨ valuation q 1501 = false ∨ valuation q 1511 = true := by
  have hs : count1505 q = (countLit q [-2, -4, -6, -8, -10, -12, -13]) + (countLit q [-15, -18, -19, -21, -23, -24, -26, -27]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-2, -4, -6, -8, -10, -12, -13]) (l₂ := [-15, -18, -19, -21, -23, -24, -26, -27])
  have hm := merge_two (literal (valuation q) (1475)) (literal (valuation q) (1501)) (literal (valuation q) (1511)) (countLit q [-2, -4, -6, -8, -10, -12, -13]) (countLit q [-15, -18, -19, -21, -23, -24, -26, -27]) (count1505 q) 2 5 (meaning1475 q) (meaning1501 q) (meaning1511 q) hs
  change valuation q 1475 = false ∨ valuation q 1501 = false ∨ valuation q 1511 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1016 (q : Snake 81) (h : Conditions q) : valuation q 1476 = false ∨ valuation q 1497 = false ∨ valuation q 1508 = true := by
  have hs : count1505 q = (countLit q [-2, -4, -6, -8, -10, -12, -13]) + (countLit q [-15, -18, -19, -21, -23, -24, -26, -27]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-2, -4, -6, -8, -10, -12, -13]) (l₂ := [-15, -18, -19, -21, -23, -24, -26, -27])
  have hm := merge_two (literal (valuation q) (1476)) (literal (valuation q) (1497)) (literal (valuation q) (1508)) (countLit q [-2, -4, -6, -8, -10, -12, -13]) (countLit q [-15, -18, -19, -21, -23, -24, -26, -27]) (count1505 q) 3 1 (meaning1476 q) (meaning1497 q) (meaning1508 q) hs
  change valuation q 1476 = false ∨ valuation q 1497 = false ∨ valuation q 1508 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1017 (q : Snake 81) (h : Conditions q) : valuation q 1476 = false ∨ valuation q 1498 = false ∨ valuation q 1509 = true := by
  have hs : count1505 q = (countLit q [-2, -4, -6, -8, -10, -12, -13]) + (countLit q [-15, -18, -19, -21, -23, -24, -26, -27]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-2, -4, -6, -8, -10, -12, -13]) (l₂ := [-15, -18, -19, -21, -23, -24, -26, -27])
  have hm := merge_two (literal (valuation q) (1476)) (literal (valuation q) (1498)) (literal (valuation q) (1509)) (countLit q [-2, -4, -6, -8, -10, -12, -13]) (countLit q [-15, -18, -19, -21, -23, -24, -26, -27]) (count1505 q) 3 2 (meaning1476 q) (meaning1498 q) (meaning1509 q) hs
  change valuation q 1476 = false ∨ valuation q 1498 = false ∨ valuation q 1509 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1018 (q : Snake 81) (h : Conditions q) : valuation q 1476 = false ∨ valuation q 1499 = false ∨ valuation q 1510 = true := by
  have hs : count1505 q = (countLit q [-2, -4, -6, -8, -10, -12, -13]) + (countLit q [-15, -18, -19, -21, -23, -24, -26, -27]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-2, -4, -6, -8, -10, -12, -13]) (l₂ := [-15, -18, -19, -21, -23, -24, -26, -27])
  have hm := merge_two (literal (valuation q) (1476)) (literal (valuation q) (1499)) (literal (valuation q) (1510)) (countLit q [-2, -4, -6, -8, -10, -12, -13]) (countLit q [-15, -18, -19, -21, -23, -24, -26, -27]) (count1505 q) 3 3 (meaning1476 q) (meaning1499 q) (meaning1510 q) hs
  change valuation q 1476 = false ∨ valuation q 1499 = false ∨ valuation q 1510 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1019 (q : Snake 81) (h : Conditions q) : valuation q 1476 = false ∨ valuation q 1500 = false ∨ valuation q 1511 = true := by
  have hs : count1505 q = (countLit q [-2, -4, -6, -8, -10, -12, -13]) + (countLit q [-15, -18, -19, -21, -23, -24, -26, -27]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-2, -4, -6, -8, -10, -12, -13]) (l₂ := [-15, -18, -19, -21, -23, -24, -26, -27])
  have hm := merge_two (literal (valuation q) (1476)) (literal (valuation q) (1500)) (literal (valuation q) (1511)) (countLit q [-2, -4, -6, -8, -10, -12, -13]) (countLit q [-15, -18, -19, -21, -23, -24, -26, -27]) (count1505 q) 3 4 (meaning1476 q) (meaning1500 q) (meaning1511 q) hs
  change valuation q 1476 = false ∨ valuation q 1500 = false ∨ valuation q 1511 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1020 (q : Snake 81) (h : Conditions q) : valuation q 1476 = false ∨ valuation q 1501 = false ∨ valuation q 1512 = true := by
  have hs : count1505 q = (countLit q [-2, -4, -6, -8, -10, -12, -13]) + (countLit q [-15, -18, -19, -21, -23, -24, -26, -27]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-2, -4, -6, -8, -10, -12, -13]) (l₂ := [-15, -18, -19, -21, -23, -24, -26, -27])
  have hm := merge_two (literal (valuation q) (1476)) (literal (valuation q) (1501)) (literal (valuation q) (1512)) (countLit q [-2, -4, -6, -8, -10, -12, -13]) (countLit q [-15, -18, -19, -21, -23, -24, -26, -27]) (count1505 q) 3 5 (meaning1476 q) (meaning1501 q) (meaning1512 q) hs
  change valuation q 1476 = false ∨ valuation q 1501 = false ∨ valuation q 1512 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1021 (q : Snake 81) (h : Conditions q) : valuation q 1476 = false ∨ valuation q 1502 = false ∨ valuation q 1513 = true := by
  have hs : count1505 q = (countLit q [-2, -4, -6, -8, -10, -12, -13]) + (countLit q [-15, -18, -19, -21, -23, -24, -26, -27]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-2, -4, -6, -8, -10, -12, -13]) (l₂ := [-15, -18, -19, -21, -23, -24, -26, -27])
  have hm := merge_two (literal (valuation q) (1476)) (literal (valuation q) (1502)) (literal (valuation q) (1513)) (countLit q [-2, -4, -6, -8, -10, -12, -13]) (countLit q [-15, -18, -19, -21, -23, -24, -26, -27]) (count1505 q) 3 6 (meaning1476 q) (meaning1502 q) (meaning1513 q) hs
  change valuation q 1476 = false ∨ valuation q 1502 = false ∨ valuation q 1513 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1022 (q : Snake 81) (h : Conditions q) : valuation q 1477 = false ∨ valuation q 1508 = true := by
  have hs : count1505 q = (countLit q [-2, -4, -6, -8, -10, -12, -13]) + (countLit q [-15, -18, -19, -21, -23, -24, -26, -27]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-2, -4, -6, -8, -10, -12, -13]) (l₂ := [-15, -18, -19, -21, -23, -24, -26, -27])
  have hm := merge_left (literal (valuation q) (1477)) (literal (valuation q) (1508)) (countLit q [-2, -4, -6, -8, -10, -12, -13]) (countLit q [-15, -18, -19, -21, -23, -24, -26, -27]) (count1505 q) 4 (meaning1477 q) (meaning1508 q) hs
  change valuation q 1477 = false ∨ valuation q 1508 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1023 (q : Snake 81) (h : Conditions q) : valuation q 1477 = false ∨ valuation q 1497 = false ∨ valuation q 1509 = true := by
  have hs : count1505 q = (countLit q [-2, -4, -6, -8, -10, -12, -13]) + (countLit q [-15, -18, -19, -21, -23, -24, -26, -27]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-2, -4, -6, -8, -10, -12, -13]) (l₂ := [-15, -18, -19, -21, -23, -24, -26, -27])
  have hm := merge_two (literal (valuation q) (1477)) (literal (valuation q) (1497)) (literal (valuation q) (1509)) (countLit q [-2, -4, -6, -8, -10, -12, -13]) (countLit q [-15, -18, -19, -21, -23, -24, -26, -27]) (count1505 q) 4 1 (meaning1477 q) (meaning1497 q) (meaning1509 q) hs
  change valuation q 1477 = false ∨ valuation q 1497 = false ∨ valuation q 1509 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1024 (q : Snake 81) (h : Conditions q) : valuation q 1477 = false ∨ valuation q 1498 = false ∨ valuation q 1510 = true := by
  have hs : count1505 q = (countLit q [-2, -4, -6, -8, -10, -12, -13]) + (countLit q [-15, -18, -19, -21, -23, -24, -26, -27]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-2, -4, -6, -8, -10, -12, -13]) (l₂ := [-15, -18, -19, -21, -23, -24, -26, -27])
  have hm := merge_two (literal (valuation q) (1477)) (literal (valuation q) (1498)) (literal (valuation q) (1510)) (countLit q [-2, -4, -6, -8, -10, -12, -13]) (countLit q [-15, -18, -19, -21, -23, -24, -26, -27]) (count1505 q) 4 2 (meaning1477 q) (meaning1498 q) (meaning1510 q) hs
  change valuation q 1477 = false ∨ valuation q 1498 = false ∨ valuation q 1510 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem block31 (q : Snake 81) (h : Conditions q) : Dfs112FirstBoolean.Block31 (valuation q) :=
  ⟨clause993 q h, clause994 q h, clause995 q h, clause996 q h, clause997 q h, clause998 q h, clause999 q h, clause1000 q h, clause1001 q h, clause1002 q h, clause1003 q h, clause1004 q h, clause1005 q h, clause1006 q h, clause1007 q h, clause1008 q h, clause1009 q h, clause1010 q h, clause1011 q h, clause1012 q h, clause1013 q h, clause1014 q h, clause1015 q h, clause1016 q h, clause1017 q h, clause1018 q h, clause1019 q h, clause1020 q h, clause1021 q h, clause1022 q h, clause1023 q h, clause1024 q h⟩

end
end Snake9.Regrowth.First112
