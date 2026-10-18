import First112Semantics
import Dfs112FirstBooleanInputs
namespace Snake9.Regrowth.First112
noncomputable section
local instance blockDec33 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause1057 (q : Snake 81) (h : Conditions q) : valuation q 1529 = false ∨ valuation q 1531 = false ∨ valuation q 1535 = true := by
  have hs : count1532 q = (countLit q [-39, -41]) + (countLit q [-42, -43]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-39, -41]) (l₂ := [-42, -43])
  have hm := merge_two (literal (valuation q) (1529)) (literal (valuation q) (1531)) (literal (valuation q) (1535)) (countLit q [-39, -41]) (countLit q [-42, -43]) (count1532 q) 2 2 (meaning1529 q) (meaning1531 q) (meaning1535 q) hs
  change valuation q 1529 = false ∨ valuation q 1531 = false ∨ valuation q 1535 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1058 (q : Snake 81) (h : Conditions q) : valuation q 1532 = false ∨ valuation q 1536 = true := by
  have hs : count1536 q = (countLit q [-31, -33, -34, -35]) + (countLit q [-39, -41, -42, -43]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-31, -33, -34, -35]) (l₂ := [-39, -41, -42, -43])
  have hm := merge_right (literal (valuation q) (1532)) (literal (valuation q) (1536)) (countLit q [-31, -33, -34, -35]) (countLit q [-39, -41, -42, -43]) (count1536 q) 1 (meaning1532 q) (meaning1536 q) hs
  change valuation q 1532 = false ∨ valuation q 1536 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1059 (q : Snake 81) (h : Conditions q) : valuation q 1533 = false ∨ valuation q 1537 = true := by
  have hs : count1536 q = (countLit q [-31, -33, -34, -35]) + (countLit q [-39, -41, -42, -43]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-31, -33, -34, -35]) (l₂ := [-39, -41, -42, -43])
  have hm := merge_right (literal (valuation q) (1533)) (literal (valuation q) (1537)) (countLit q [-31, -33, -34, -35]) (countLit q [-39, -41, -42, -43]) (count1536 q) 2 (meaning1533 q) (meaning1537 q) hs
  change valuation q 1533 = false ∨ valuation q 1537 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1060 (q : Snake 81) (h : Conditions q) : valuation q 1534 = false ∨ valuation q 1538 = true := by
  have hs : count1536 q = (countLit q [-31, -33, -34, -35]) + (countLit q [-39, -41, -42, -43]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-31, -33, -34, -35]) (l₂ := [-39, -41, -42, -43])
  have hm := merge_right (literal (valuation q) (1534)) (literal (valuation q) (1538)) (countLit q [-31, -33, -34, -35]) (countLit q [-39, -41, -42, -43]) (count1536 q) 3 (meaning1534 q) (meaning1538 q) hs
  change valuation q 1534 = false ∨ valuation q 1538 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1061 (q : Snake 81) (h : Conditions q) : valuation q 1524 = false ∨ valuation q 1536 = true := by
  have hs : count1536 q = (countLit q [-31, -33, -34, -35]) + (countLit q [-39, -41, -42, -43]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-31, -33, -34, -35]) (l₂ := [-39, -41, -42, -43])
  have hm := merge_left (literal (valuation q) (1524)) (literal (valuation q) (1536)) (countLit q [-31, -33, -34, -35]) (countLit q [-39, -41, -42, -43]) (count1536 q) 1 (meaning1524 q) (meaning1536 q) hs
  change valuation q 1524 = false ∨ valuation q 1536 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1062 (q : Snake 81) (h : Conditions q) : valuation q 1524 = false ∨ valuation q 1532 = false ∨ valuation q 1537 = true := by
  have hs : count1536 q = (countLit q [-31, -33, -34, -35]) + (countLit q [-39, -41, -42, -43]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-31, -33, -34, -35]) (l₂ := [-39, -41, -42, -43])
  have hm := merge_two (literal (valuation q) (1524)) (literal (valuation q) (1532)) (literal (valuation q) (1537)) (countLit q [-31, -33, -34, -35]) (countLit q [-39, -41, -42, -43]) (count1536 q) 1 1 (meaning1524 q) (meaning1532 q) (meaning1537 q) hs
  change valuation q 1524 = false ∨ valuation q 1532 = false ∨ valuation q 1537 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1063 (q : Snake 81) (h : Conditions q) : valuation q 1524 = false ∨ valuation q 1533 = false ∨ valuation q 1538 = true := by
  have hs : count1536 q = (countLit q [-31, -33, -34, -35]) + (countLit q [-39, -41, -42, -43]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-31, -33, -34, -35]) (l₂ := [-39, -41, -42, -43])
  have hm := merge_two (literal (valuation q) (1524)) (literal (valuation q) (1533)) (literal (valuation q) (1538)) (countLit q [-31, -33, -34, -35]) (countLit q [-39, -41, -42, -43]) (count1536 q) 1 2 (meaning1524 q) (meaning1533 q) (meaning1538 q) hs
  change valuation q 1524 = false ∨ valuation q 1533 = false ∨ valuation q 1538 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1064 (q : Snake 81) (h : Conditions q) : valuation q 1524 = false ∨ valuation q 1534 = false ∨ valuation q 1539 = true := by
  have hs : count1536 q = (countLit q [-31, -33, -34, -35]) + (countLit q [-39, -41, -42, -43]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-31, -33, -34, -35]) (l₂ := [-39, -41, -42, -43])
  have hm := merge_two (literal (valuation q) (1524)) (literal (valuation q) (1534)) (literal (valuation q) (1539)) (countLit q [-31, -33, -34, -35]) (countLit q [-39, -41, -42, -43]) (count1536 q) 1 3 (meaning1524 q) (meaning1534 q) (meaning1539 q) hs
  change valuation q 1524 = false ∨ valuation q 1534 = false ∨ valuation q 1539 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1065 (q : Snake 81) (h : Conditions q) : valuation q 1524 = false ∨ valuation q 1535 = false ∨ valuation q 1540 = true := by
  have hs : count1536 q = (countLit q [-31, -33, -34, -35]) + (countLit q [-39, -41, -42, -43]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-31, -33, -34, -35]) (l₂ := [-39, -41, -42, -43])
  have hm := merge_two (literal (valuation q) (1524)) (literal (valuation q) (1535)) (literal (valuation q) (1540)) (countLit q [-31, -33, -34, -35]) (countLit q [-39, -41, -42, -43]) (count1536 q) 1 4 (meaning1524 q) (meaning1535 q) (meaning1540 q) hs
  change valuation q 1524 = false ∨ valuation q 1535 = false ∨ valuation q 1540 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1066 (q : Snake 81) (h : Conditions q) : valuation q 1525 = false ∨ valuation q 1537 = true := by
  have hs : count1536 q = (countLit q [-31, -33, -34, -35]) + (countLit q [-39, -41, -42, -43]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-31, -33, -34, -35]) (l₂ := [-39, -41, -42, -43])
  have hm := merge_left (literal (valuation q) (1525)) (literal (valuation q) (1537)) (countLit q [-31, -33, -34, -35]) (countLit q [-39, -41, -42, -43]) (count1536 q) 2 (meaning1525 q) (meaning1537 q) hs
  change valuation q 1525 = false ∨ valuation q 1537 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1067 (q : Snake 81) (h : Conditions q) : valuation q 1525 = false ∨ valuation q 1532 = false ∨ valuation q 1538 = true := by
  have hs : count1536 q = (countLit q [-31, -33, -34, -35]) + (countLit q [-39, -41, -42, -43]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-31, -33, -34, -35]) (l₂ := [-39, -41, -42, -43])
  have hm := merge_two (literal (valuation q) (1525)) (literal (valuation q) (1532)) (literal (valuation q) (1538)) (countLit q [-31, -33, -34, -35]) (countLit q [-39, -41, -42, -43]) (count1536 q) 2 1 (meaning1525 q) (meaning1532 q) (meaning1538 q) hs
  change valuation q 1525 = false ∨ valuation q 1532 = false ∨ valuation q 1538 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1068 (q : Snake 81) (h : Conditions q) : valuation q 1525 = false ∨ valuation q 1533 = false ∨ valuation q 1539 = true := by
  have hs : count1536 q = (countLit q [-31, -33, -34, -35]) + (countLit q [-39, -41, -42, -43]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-31, -33, -34, -35]) (l₂ := [-39, -41, -42, -43])
  have hm := merge_two (literal (valuation q) (1525)) (literal (valuation q) (1533)) (literal (valuation q) (1539)) (countLit q [-31, -33, -34, -35]) (countLit q [-39, -41, -42, -43]) (count1536 q) 2 2 (meaning1525 q) (meaning1533 q) (meaning1539 q) hs
  change valuation q 1525 = false ∨ valuation q 1533 = false ∨ valuation q 1539 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1069 (q : Snake 81) (h : Conditions q) : valuation q 1525 = false ∨ valuation q 1534 = false ∨ valuation q 1540 = true := by
  have hs : count1536 q = (countLit q [-31, -33, -34, -35]) + (countLit q [-39, -41, -42, -43]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-31, -33, -34, -35]) (l₂ := [-39, -41, -42, -43])
  have hm := merge_two (literal (valuation q) (1525)) (literal (valuation q) (1534)) (literal (valuation q) (1540)) (countLit q [-31, -33, -34, -35]) (countLit q [-39, -41, -42, -43]) (count1536 q) 2 3 (meaning1525 q) (meaning1534 q) (meaning1540 q) hs
  change valuation q 1525 = false ∨ valuation q 1534 = false ∨ valuation q 1540 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1070 (q : Snake 81) (h : Conditions q) : valuation q 47 = true ∨ valuation q 1544 = true := by
  have hs : count1544 q = (countLit q [-45]) + (countLit q [-47]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-45]) (l₂ := [-47])
  have hm := merge_right (literal (valuation q) (-47)) (literal (valuation q) (1544)) (countLit q [-45]) (countLit q [-47]) (count1544 q) 1 (meaningNeg47 q) (meaning1544 q) hs
  change (! (valuation q 47)) = false ∨ valuation q 1544 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1071 (q : Snake 81) (h : Conditions q) : valuation q 45 = true ∨ valuation q 1544 = true := by
  have hs : count1544 q = (countLit q [-45]) + (countLit q [-47]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-45]) (l₂ := [-47])
  have hm := merge_left (literal (valuation q) (-45)) (literal (valuation q) (1544)) (countLit q [-45]) (countLit q [-47]) (count1544 q) 1 (meaningNeg45 q) (meaning1544 q) hs
  change (! (valuation q 45)) = false ∨ valuation q 1544 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1072 (q : Snake 81) (h : Conditions q) : valuation q 45 = true ∨ valuation q 47 = true ∨ valuation q 1545 = true := by
  have hs : count1544 q = (countLit q [-45]) + (countLit q [-47]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-45]) (l₂ := [-47])
  have hm := merge_two (literal (valuation q) (-45)) (literal (valuation q) (-47)) (literal (valuation q) (1545)) (countLit q [-45]) (countLit q [-47]) (count1544 q) 1 1 (meaningNeg45 q) (meaningNeg47 q) (meaning1545 q) hs
  change (! (valuation q 45)) = false ∨ (! (valuation q 47)) = false ∨ valuation q 1545 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1073 (q : Snake 81) (h : Conditions q) : valuation q 50 = true ∨ valuation q 1546 = true := by
  have hs : count1546 q = (countLit q [-49]) + (countLit q [-50]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-49]) (l₂ := [-50])
  have hm := merge_right (literal (valuation q) (-50)) (literal (valuation q) (1546)) (countLit q [-49]) (countLit q [-50]) (count1546 q) 1 (meaningNeg50 q) (meaning1546 q) hs
  change (! (valuation q 50)) = false ∨ valuation q 1546 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1074 (q : Snake 81) (h : Conditions q) : valuation q 49 = true ∨ valuation q 1546 = true := by
  have hs : count1546 q = (countLit q [-49]) + (countLit q [-50]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-49]) (l₂ := [-50])
  have hm := merge_left (literal (valuation q) (-49)) (literal (valuation q) (1546)) (countLit q [-49]) (countLit q [-50]) (count1546 q) 1 (meaningNeg49 q) (meaning1546 q) hs
  change (! (valuation q 49)) = false ∨ valuation q 1546 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1075 (q : Snake 81) (h : Conditions q) : valuation q 49 = true ∨ valuation q 50 = true ∨ valuation q 1547 = true := by
  have hs : count1546 q = (countLit q [-49]) + (countLit q [-50]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-49]) (l₂ := [-50])
  have hm := merge_two (literal (valuation q) (-49)) (literal (valuation q) (-50)) (literal (valuation q) (1547)) (countLit q [-49]) (countLit q [-50]) (count1546 q) 1 1 (meaningNeg49 q) (meaningNeg50 q) (meaning1547 q) hs
  change (! (valuation q 49)) = false ∨ (! (valuation q 50)) = false ∨ valuation q 1547 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1076 (q : Snake 81) (h : Conditions q) : valuation q 1546 = false ∨ valuation q 1548 = true := by
  have hs : count1548 q = (countLit q [-45, -47]) + (countLit q [-49, -50]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-45, -47]) (l₂ := [-49, -50])
  have hm := merge_right (literal (valuation q) (1546)) (literal (valuation q) (1548)) (countLit q [-45, -47]) (countLit q [-49, -50]) (count1548 q) 1 (meaning1546 q) (meaning1548 q) hs
  change valuation q 1546 = false ∨ valuation q 1548 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1077 (q : Snake 81) (h : Conditions q) : valuation q 1547 = false ∨ valuation q 1549 = true := by
  have hs : count1548 q = (countLit q [-45, -47]) + (countLit q [-49, -50]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-45, -47]) (l₂ := [-49, -50])
  have hm := merge_right (literal (valuation q) (1547)) (literal (valuation q) (1549)) (countLit q [-45, -47]) (countLit q [-49, -50]) (count1548 q) 2 (meaning1547 q) (meaning1549 q) hs
  change valuation q 1547 = false ∨ valuation q 1549 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1078 (q : Snake 81) (h : Conditions q) : valuation q 1544 = false ∨ valuation q 1548 = true := by
  have hs : count1548 q = (countLit q [-45, -47]) + (countLit q [-49, -50]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-45, -47]) (l₂ := [-49, -50])
  have hm := merge_left (literal (valuation q) (1544)) (literal (valuation q) (1548)) (countLit q [-45, -47]) (countLit q [-49, -50]) (count1548 q) 1 (meaning1544 q) (meaning1548 q) hs
  change valuation q 1544 = false ∨ valuation q 1548 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1079 (q : Snake 81) (h : Conditions q) : valuation q 1544 = false ∨ valuation q 1546 = false ∨ valuation q 1549 = true := by
  have hs : count1548 q = (countLit q [-45, -47]) + (countLit q [-49, -50]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-45, -47]) (l₂ := [-49, -50])
  have hm := merge_two (literal (valuation q) (1544)) (literal (valuation q) (1546)) (literal (valuation q) (1549)) (countLit q [-45, -47]) (countLit q [-49, -50]) (count1548 q) 1 1 (meaning1544 q) (meaning1546 q) (meaning1549 q) hs
  change valuation q 1544 = false ∨ valuation q 1546 = false ∨ valuation q 1549 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1080 (q : Snake 81) (h : Conditions q) : valuation q 1544 = false ∨ valuation q 1547 = false ∨ valuation q 1550 = true := by
  have hs : count1548 q = (countLit q [-45, -47]) + (countLit q [-49, -50]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-45, -47]) (l₂ := [-49, -50])
  have hm := merge_two (literal (valuation q) (1544)) (literal (valuation q) (1547)) (literal (valuation q) (1550)) (countLit q [-45, -47]) (countLit q [-49, -50]) (count1548 q) 1 2 (meaning1544 q) (meaning1547 q) (meaning1550 q) hs
  change valuation q 1544 = false ∨ valuation q 1547 = false ∨ valuation q 1550 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1081 (q : Snake 81) (h : Conditions q) : valuation q 1545 = false ∨ valuation q 1549 = true := by
  have hs : count1548 q = (countLit q [-45, -47]) + (countLit q [-49, -50]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-45, -47]) (l₂ := [-49, -50])
  have hm := merge_left (literal (valuation q) (1545)) (literal (valuation q) (1549)) (countLit q [-45, -47]) (countLit q [-49, -50]) (count1548 q) 2 (meaning1545 q) (meaning1549 q) hs
  change valuation q 1545 = false ∨ valuation q 1549 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1082 (q : Snake 81) (h : Conditions q) : valuation q 1545 = false ∨ valuation q 1546 = false ∨ valuation q 1550 = true := by
  have hs : count1548 q = (countLit q [-45, -47]) + (countLit q [-49, -50]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-45, -47]) (l₂ := [-49, -50])
  have hm := merge_two (literal (valuation q) (1545)) (literal (valuation q) (1546)) (literal (valuation q) (1550)) (countLit q [-45, -47]) (countLit q [-49, -50]) (count1548 q) 2 1 (meaning1545 q) (meaning1546 q) (meaning1550 q) hs
  change valuation q 1545 = false ∨ valuation q 1546 = false ∨ valuation q 1550 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1083 (q : Snake 81) (h : Conditions q) : valuation q 1545 = false ∨ valuation q 1547 = false ∨ valuation q 1551 = true := by
  have hs : count1548 q = (countLit q [-45, -47]) + (countLit q [-49, -50]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-45, -47]) (l₂ := [-49, -50])
  have hm := merge_two (literal (valuation q) (1545)) (literal (valuation q) (1547)) (literal (valuation q) (1551)) (countLit q [-45, -47]) (countLit q [-49, -50]) (count1548 q) 2 2 (meaning1545 q) (meaning1547 q) (meaning1551 q) hs
  change valuation q 1545 = false ∨ valuation q 1547 = false ∨ valuation q 1551 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1084 (q : Snake 81) (h : Conditions q) : valuation q 56 = true ∨ valuation q 1552 = true := by
  have hs : count1552 q = (countLit q [-53]) + (countLit q [-56]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-53]) (l₂ := [-56])
  have hm := merge_right (literal (valuation q) (-56)) (literal (valuation q) (1552)) (countLit q [-53]) (countLit q [-56]) (count1552 q) 1 (meaningNeg56 q) (meaning1552 q) hs
  change (! (valuation q 56)) = false ∨ valuation q 1552 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1085 (q : Snake 81) (h : Conditions q) : valuation q 53 = true ∨ valuation q 1552 = true := by
  have hs : count1552 q = (countLit q [-53]) + (countLit q [-56]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-53]) (l₂ := [-56])
  have hm := merge_left (literal (valuation q) (-53)) (literal (valuation q) (1552)) (countLit q [-53]) (countLit q [-56]) (count1552 q) 1 (meaningNeg53 q) (meaning1552 q) hs
  change (! (valuation q 53)) = false ∨ valuation q 1552 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1086 (q : Snake 81) (h : Conditions q) : valuation q 53 = true ∨ valuation q 56 = true ∨ valuation q 1553 = true := by
  have hs : count1552 q = (countLit q [-53]) + (countLit q [-56]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-53]) (l₂ := [-56])
  have hm := merge_two (literal (valuation q) (-53)) (literal (valuation q) (-56)) (literal (valuation q) (1553)) (countLit q [-53]) (countLit q [-56]) (count1552 q) 1 1 (meaningNeg53 q) (meaningNeg56 q) (meaning1553 q) hs
  change (! (valuation q 53)) = false ∨ (! (valuation q 56)) = false ∨ valuation q 1553 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1087 (q : Snake 81) (h : Conditions q) : valuation q 60 = true ∨ valuation q 1554 = true := by
  have hs : count1554 q = (countLit q [-59]) + (countLit q [-60]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-59]) (l₂ := [-60])
  have hm := merge_right (literal (valuation q) (-60)) (literal (valuation q) (1554)) (countLit q [-59]) (countLit q [-60]) (count1554 q) 1 (meaningNeg60 q) (meaning1554 q) hs
  change (! (valuation q 60)) = false ∨ valuation q 1554 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1088 (q : Snake 81) (h : Conditions q) : valuation q 59 = true ∨ valuation q 1554 = true := by
  have hs : count1554 q = (countLit q [-59]) + (countLit q [-60]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-59]) (l₂ := [-60])
  have hm := merge_left (literal (valuation q) (-59)) (literal (valuation q) (1554)) (countLit q [-59]) (countLit q [-60]) (count1554 q) 1 (meaningNeg59 q) (meaning1554 q) hs
  change (! (valuation q 59)) = false ∨ valuation q 1554 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem block33 (q : Snake 81) (h : Conditions q) : Dfs112FirstBoolean.Block33 (valuation q) :=
  ⟨clause1057 q h, clause1058 q h, clause1059 q h, clause1060 q h, clause1061 q h, clause1062 q h, clause1063 q h, clause1064 q h, clause1065 q h, clause1066 q h, clause1067 q h, clause1068 q h, clause1069 q h, clause1070 q h, clause1071 q h, clause1072 q h, clause1073 q h, clause1074 q h, clause1075 q h, clause1076 q h, clause1077 q h, clause1078 q h, clause1079 q h, clause1080 q h, clause1081 q h, clause1082 q h, clause1083 q h, clause1084 q h, clause1085 q h, clause1086 q h, clause1087 q h, clause1088 q h⟩

end
end Snake9.Regrowth.First112
