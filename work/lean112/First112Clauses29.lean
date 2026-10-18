import First112Semantics
import Dfs112FirstBooleanInputs
namespace Snake9.Regrowth.First112
noncomputable section
local instance blockDec29 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause929 (q : Snake 81) (h : Conditions q) : valuation q 4 = true ∨ valuation q 1461 = true := by
  have hs : count1461 q = (countLit q [-4]) + (countLit q [-6]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-4]) (l₂ := [-6])
  have hm := merge_left (literal (valuation q) (-4)) (literal (valuation q) (1461)) (countLit q [-4]) (countLit q [-6]) (count1461 q) 1 (meaningNeg4 q) (meaning1461 q) hs
  change (! (valuation q 4)) = false ∨ valuation q 1461 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause930 (q : Snake 81) (h : Conditions q) : valuation q 4 = true ∨ valuation q 6 = true ∨ valuation q 1462 = true := by
  have hs : count1461 q = (countLit q [-4]) + (countLit q [-6]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-4]) (l₂ := [-6])
  have hm := merge_two (literal (valuation q) (-4)) (literal (valuation q) (-6)) (literal (valuation q) (1462)) (countLit q [-4]) (countLit q [-6]) (count1461 q) 1 1 (meaningNeg4 q) (meaningNeg6 q) (meaning1462 q) hs
  change (! (valuation q 4)) = false ∨ (! (valuation q 6)) = false ∨ valuation q 1462 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause931 (q : Snake 81) (h : Conditions q) : valuation q 1461 = false ∨ valuation q 1463 = true := by
  have hs : count1463 q = (countLit q [-2]) + (countLit q [-4, -6]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-2]) (l₂ := [-4, -6])
  have hm := merge_right (literal (valuation q) (1461)) (literal (valuation q) (1463)) (countLit q [-2]) (countLit q [-4, -6]) (count1463 q) 1 (meaning1461 q) (meaning1463 q) hs
  change valuation q 1461 = false ∨ valuation q 1463 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause932 (q : Snake 81) (h : Conditions q) : valuation q 1462 = false ∨ valuation q 1464 = true := by
  have hs : count1463 q = (countLit q [-2]) + (countLit q [-4, -6]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-2]) (l₂ := [-4, -6])
  have hm := merge_right (literal (valuation q) (1462)) (literal (valuation q) (1464)) (countLit q [-2]) (countLit q [-4, -6]) (count1463 q) 2 (meaning1462 q) (meaning1464 q) hs
  change valuation q 1462 = false ∨ valuation q 1464 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause933 (q : Snake 81) (h : Conditions q) : valuation q 2 = true ∨ valuation q 1463 = true := by
  have hs : count1463 q = (countLit q [-2]) + (countLit q [-4, -6]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-2]) (l₂ := [-4, -6])
  have hm := merge_left (literal (valuation q) (-2)) (literal (valuation q) (1463)) (countLit q [-2]) (countLit q [-4, -6]) (count1463 q) 1 (meaningNeg2 q) (meaning1463 q) hs
  change (! (valuation q 2)) = false ∨ valuation q 1463 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause934 (q : Snake 81) (h : Conditions q) : valuation q 2 = true ∨ valuation q 1461 = false ∨ valuation q 1464 = true := by
  have hs : count1463 q = (countLit q [-2]) + (countLit q [-4, -6]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-2]) (l₂ := [-4, -6])
  have hm := merge_two (literal (valuation q) (-2)) (literal (valuation q) (1461)) (literal (valuation q) (1464)) (countLit q [-2]) (countLit q [-4, -6]) (count1463 q) 1 1 (meaningNeg2 q) (meaning1461 q) (meaning1464 q) hs
  change (! (valuation q 2)) = false ∨ valuation q 1461 = false ∨ valuation q 1464 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause935 (q : Snake 81) (h : Conditions q) : valuation q 2 = true ∨ valuation q 1462 = false ∨ valuation q 1465 = true := by
  have hs : count1463 q = (countLit q [-2]) + (countLit q [-4, -6]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-2]) (l₂ := [-4, -6])
  have hm := merge_two (literal (valuation q) (-2)) (literal (valuation q) (1462)) (literal (valuation q) (1465)) (countLit q [-2]) (countLit q [-4, -6]) (count1463 q) 1 2 (meaningNeg2 q) (meaning1462 q) (meaning1465 q) hs
  change (! (valuation q 2)) = false ∨ valuation q 1462 = false ∨ valuation q 1465 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause936 (q : Snake 81) (h : Conditions q) : valuation q 10 = true ∨ valuation q 1466 = true := by
  have hs : count1466 q = (countLit q [-8]) + (countLit q [-10]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-8]) (l₂ := [-10])
  have hm := merge_right (literal (valuation q) (-10)) (literal (valuation q) (1466)) (countLit q [-8]) (countLit q [-10]) (count1466 q) 1 (meaningNeg10 q) (meaning1466 q) hs
  change (! (valuation q 10)) = false ∨ valuation q 1466 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause937 (q : Snake 81) (h : Conditions q) : valuation q 8 = true ∨ valuation q 1466 = true := by
  have hs : count1466 q = (countLit q [-8]) + (countLit q [-10]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-8]) (l₂ := [-10])
  have hm := merge_left (literal (valuation q) (-8)) (literal (valuation q) (1466)) (countLit q [-8]) (countLit q [-10]) (count1466 q) 1 (meaningNeg8 q) (meaning1466 q) hs
  change (! (valuation q 8)) = false ∨ valuation q 1466 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause938 (q : Snake 81) (h : Conditions q) : valuation q 8 = true ∨ valuation q 10 = true ∨ valuation q 1467 = true := by
  have hs : count1466 q = (countLit q [-8]) + (countLit q [-10]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-8]) (l₂ := [-10])
  have hm := merge_two (literal (valuation q) (-8)) (literal (valuation q) (-10)) (literal (valuation q) (1467)) (countLit q [-8]) (countLit q [-10]) (count1466 q) 1 1 (meaningNeg8 q) (meaningNeg10 q) (meaning1467 q) hs
  change (! (valuation q 8)) = false ∨ (! (valuation q 10)) = false ∨ valuation q 1467 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause939 (q : Snake 81) (h : Conditions q) : valuation q 13 = true ∨ valuation q 1468 = true := by
  have hs : count1468 q = (countLit q [-12]) + (countLit q [-13]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-12]) (l₂ := [-13])
  have hm := merge_right (literal (valuation q) (-13)) (literal (valuation q) (1468)) (countLit q [-12]) (countLit q [-13]) (count1468 q) 1 (meaningNeg13 q) (meaning1468 q) hs
  change (! (valuation q 13)) = false ∨ valuation q 1468 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause940 (q : Snake 81) (h : Conditions q) : valuation q 12 = true ∨ valuation q 1468 = true := by
  have hs : count1468 q = (countLit q [-12]) + (countLit q [-13]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-12]) (l₂ := [-13])
  have hm := merge_left (literal (valuation q) (-12)) (literal (valuation q) (1468)) (countLit q [-12]) (countLit q [-13]) (count1468 q) 1 (meaningNeg12 q) (meaning1468 q) hs
  change (! (valuation q 12)) = false ∨ valuation q 1468 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause941 (q : Snake 81) (h : Conditions q) : valuation q 12 = true ∨ valuation q 13 = true ∨ valuation q 1469 = true := by
  have hs : count1468 q = (countLit q [-12]) + (countLit q [-13]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-12]) (l₂ := [-13])
  have hm := merge_two (literal (valuation q) (-12)) (literal (valuation q) (-13)) (literal (valuation q) (1469)) (countLit q [-12]) (countLit q [-13]) (count1468 q) 1 1 (meaningNeg12 q) (meaningNeg13 q) (meaning1469 q) hs
  change (! (valuation q 12)) = false ∨ (! (valuation q 13)) = false ∨ valuation q 1469 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause942 (q : Snake 81) (h : Conditions q) : valuation q 1468 = false ∨ valuation q 1470 = true := by
  have hs : count1470 q = (countLit q [-8, -10]) + (countLit q [-12, -13]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-8, -10]) (l₂ := [-12, -13])
  have hm := merge_right (literal (valuation q) (1468)) (literal (valuation q) (1470)) (countLit q [-8, -10]) (countLit q [-12, -13]) (count1470 q) 1 (meaning1468 q) (meaning1470 q) hs
  change valuation q 1468 = false ∨ valuation q 1470 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause943 (q : Snake 81) (h : Conditions q) : valuation q 1469 = false ∨ valuation q 1471 = true := by
  have hs : count1470 q = (countLit q [-8, -10]) + (countLit q [-12, -13]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-8, -10]) (l₂ := [-12, -13])
  have hm := merge_right (literal (valuation q) (1469)) (literal (valuation q) (1471)) (countLit q [-8, -10]) (countLit q [-12, -13]) (count1470 q) 2 (meaning1469 q) (meaning1471 q) hs
  change valuation q 1469 = false ∨ valuation q 1471 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause944 (q : Snake 81) (h : Conditions q) : valuation q 1466 = false ∨ valuation q 1470 = true := by
  have hs : count1470 q = (countLit q [-8, -10]) + (countLit q [-12, -13]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-8, -10]) (l₂ := [-12, -13])
  have hm := merge_left (literal (valuation q) (1466)) (literal (valuation q) (1470)) (countLit q [-8, -10]) (countLit q [-12, -13]) (count1470 q) 1 (meaning1466 q) (meaning1470 q) hs
  change valuation q 1466 = false ∨ valuation q 1470 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause945 (q : Snake 81) (h : Conditions q) : valuation q 1466 = false ∨ valuation q 1468 = false ∨ valuation q 1471 = true := by
  have hs : count1470 q = (countLit q [-8, -10]) + (countLit q [-12, -13]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-8, -10]) (l₂ := [-12, -13])
  have hm := merge_two (literal (valuation q) (1466)) (literal (valuation q) (1468)) (literal (valuation q) (1471)) (countLit q [-8, -10]) (countLit q [-12, -13]) (count1470 q) 1 1 (meaning1466 q) (meaning1468 q) (meaning1471 q) hs
  change valuation q 1466 = false ∨ valuation q 1468 = false ∨ valuation q 1471 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause946 (q : Snake 81) (h : Conditions q) : valuation q 1466 = false ∨ valuation q 1469 = false ∨ valuation q 1472 = true := by
  have hs : count1470 q = (countLit q [-8, -10]) + (countLit q [-12, -13]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-8, -10]) (l₂ := [-12, -13])
  have hm := merge_two (literal (valuation q) (1466)) (literal (valuation q) (1469)) (literal (valuation q) (1472)) (countLit q [-8, -10]) (countLit q [-12, -13]) (count1470 q) 1 2 (meaning1466 q) (meaning1469 q) (meaning1472 q) hs
  change valuation q 1466 = false ∨ valuation q 1469 = false ∨ valuation q 1472 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause947 (q : Snake 81) (h : Conditions q) : valuation q 1467 = false ∨ valuation q 1471 = true := by
  have hs : count1470 q = (countLit q [-8, -10]) + (countLit q [-12, -13]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-8, -10]) (l₂ := [-12, -13])
  have hm := merge_left (literal (valuation q) (1467)) (literal (valuation q) (1471)) (countLit q [-8, -10]) (countLit q [-12, -13]) (count1470 q) 2 (meaning1467 q) (meaning1471 q) hs
  change valuation q 1467 = false ∨ valuation q 1471 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause948 (q : Snake 81) (h : Conditions q) : valuation q 1467 = false ∨ valuation q 1468 = false ∨ valuation q 1472 = true := by
  have hs : count1470 q = (countLit q [-8, -10]) + (countLit q [-12, -13]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-8, -10]) (l₂ := [-12, -13])
  have hm := merge_two (literal (valuation q) (1467)) (literal (valuation q) (1468)) (literal (valuation q) (1472)) (countLit q [-8, -10]) (countLit q [-12, -13]) (count1470 q) 2 1 (meaning1467 q) (meaning1468 q) (meaning1472 q) hs
  change valuation q 1467 = false ∨ valuation q 1468 = false ∨ valuation q 1472 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause949 (q : Snake 81) (h : Conditions q) : valuation q 1467 = false ∨ valuation q 1469 = false ∨ valuation q 1473 = true := by
  have hs : count1470 q = (countLit q [-8, -10]) + (countLit q [-12, -13]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-8, -10]) (l₂ := [-12, -13])
  have hm := merge_two (literal (valuation q) (1467)) (literal (valuation q) (1469)) (literal (valuation q) (1473)) (countLit q [-8, -10]) (countLit q [-12, -13]) (count1470 q) 2 2 (meaning1467 q) (meaning1469 q) (meaning1473 q) hs
  change valuation q 1467 = false ∨ valuation q 1469 = false ∨ valuation q 1473 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause950 (q : Snake 81) (h : Conditions q) : valuation q 1470 = false ∨ valuation q 1474 = true := by
  have hs : count1474 q = (countLit q [-2, -4, -6]) + (countLit q [-8, -10, -12, -13]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-2, -4, -6]) (l₂ := [-8, -10, -12, -13])
  have hm := merge_right (literal (valuation q) (1470)) (literal (valuation q) (1474)) (countLit q [-2, -4, -6]) (countLit q [-8, -10, -12, -13]) (count1474 q) 1 (meaning1470 q) (meaning1474 q) hs
  change valuation q 1470 = false ∨ valuation q 1474 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause951 (q : Snake 81) (h : Conditions q) : valuation q 1471 = false ∨ valuation q 1475 = true := by
  have hs : count1474 q = (countLit q [-2, -4, -6]) + (countLit q [-8, -10, -12, -13]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-2, -4, -6]) (l₂ := [-8, -10, -12, -13])
  have hm := merge_right (literal (valuation q) (1471)) (literal (valuation q) (1475)) (countLit q [-2, -4, -6]) (countLit q [-8, -10, -12, -13]) (count1474 q) 2 (meaning1471 q) (meaning1475 q) hs
  change valuation q 1471 = false ∨ valuation q 1475 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause952 (q : Snake 81) (h : Conditions q) : valuation q 1472 = false ∨ valuation q 1476 = true := by
  have hs : count1474 q = (countLit q [-2, -4, -6]) + (countLit q [-8, -10, -12, -13]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-2, -4, -6]) (l₂ := [-8, -10, -12, -13])
  have hm := merge_right (literal (valuation q) (1472)) (literal (valuation q) (1476)) (countLit q [-2, -4, -6]) (countLit q [-8, -10, -12, -13]) (count1474 q) 3 (meaning1472 q) (meaning1476 q) hs
  change valuation q 1472 = false ∨ valuation q 1476 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause953 (q : Snake 81) (h : Conditions q) : valuation q 1473 = false ∨ valuation q 1477 = true := by
  have hs : count1474 q = (countLit q [-2, -4, -6]) + (countLit q [-8, -10, -12, -13]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-2, -4, -6]) (l₂ := [-8, -10, -12, -13])
  have hm := merge_right (literal (valuation q) (1473)) (literal (valuation q) (1477)) (countLit q [-2, -4, -6]) (countLit q [-8, -10, -12, -13]) (count1474 q) 4 (meaning1473 q) (meaning1477 q) hs
  change valuation q 1473 = false ∨ valuation q 1477 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause954 (q : Snake 81) (h : Conditions q) : valuation q 1463 = false ∨ valuation q 1474 = true := by
  have hs : count1474 q = (countLit q [-2, -4, -6]) + (countLit q [-8, -10, -12, -13]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-2, -4, -6]) (l₂ := [-8, -10, -12, -13])
  have hm := merge_left (literal (valuation q) (1463)) (literal (valuation q) (1474)) (countLit q [-2, -4, -6]) (countLit q [-8, -10, -12, -13]) (count1474 q) 1 (meaning1463 q) (meaning1474 q) hs
  change valuation q 1463 = false ∨ valuation q 1474 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause955 (q : Snake 81) (h : Conditions q) : valuation q 1463 = false ∨ valuation q 1470 = false ∨ valuation q 1475 = true := by
  have hs : count1474 q = (countLit q [-2, -4, -6]) + (countLit q [-8, -10, -12, -13]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-2, -4, -6]) (l₂ := [-8, -10, -12, -13])
  have hm := merge_two (literal (valuation q) (1463)) (literal (valuation q) (1470)) (literal (valuation q) (1475)) (countLit q [-2, -4, -6]) (countLit q [-8, -10, -12, -13]) (count1474 q) 1 1 (meaning1463 q) (meaning1470 q) (meaning1475 q) hs
  change valuation q 1463 = false ∨ valuation q 1470 = false ∨ valuation q 1475 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause956 (q : Snake 81) (h : Conditions q) : valuation q 1463 = false ∨ valuation q 1471 = false ∨ valuation q 1476 = true := by
  have hs : count1474 q = (countLit q [-2, -4, -6]) + (countLit q [-8, -10, -12, -13]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-2, -4, -6]) (l₂ := [-8, -10, -12, -13])
  have hm := merge_two (literal (valuation q) (1463)) (literal (valuation q) (1471)) (literal (valuation q) (1476)) (countLit q [-2, -4, -6]) (countLit q [-8, -10, -12, -13]) (count1474 q) 1 2 (meaning1463 q) (meaning1471 q) (meaning1476 q) hs
  change valuation q 1463 = false ∨ valuation q 1471 = false ∨ valuation q 1476 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause957 (q : Snake 81) (h : Conditions q) : valuation q 1463 = false ∨ valuation q 1472 = false ∨ valuation q 1477 = true := by
  have hs : count1474 q = (countLit q [-2, -4, -6]) + (countLit q [-8, -10, -12, -13]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-2, -4, -6]) (l₂ := [-8, -10, -12, -13])
  have hm := merge_two (literal (valuation q) (1463)) (literal (valuation q) (1472)) (literal (valuation q) (1477)) (countLit q [-2, -4, -6]) (countLit q [-8, -10, -12, -13]) (count1474 q) 1 3 (meaning1463 q) (meaning1472 q) (meaning1477 q) hs
  change valuation q 1463 = false ∨ valuation q 1472 = false ∨ valuation q 1477 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause958 (q : Snake 81) (h : Conditions q) : valuation q 1463 = false ∨ valuation q 1473 = false ∨ valuation q 1478 = true := by
  have hs : count1474 q = (countLit q [-2, -4, -6]) + (countLit q [-8, -10, -12, -13]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-2, -4, -6]) (l₂ := [-8, -10, -12, -13])
  have hm := merge_two (literal (valuation q) (1463)) (literal (valuation q) (1473)) (literal (valuation q) (1478)) (countLit q [-2, -4, -6]) (countLit q [-8, -10, -12, -13]) (count1474 q) 1 4 (meaning1463 q) (meaning1473 q) (meaning1478 q) hs
  change valuation q 1463 = false ∨ valuation q 1473 = false ∨ valuation q 1478 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause959 (q : Snake 81) (h : Conditions q) : valuation q 1464 = false ∨ valuation q 1475 = true := by
  have hs : count1474 q = (countLit q [-2, -4, -6]) + (countLit q [-8, -10, -12, -13]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-2, -4, -6]) (l₂ := [-8, -10, -12, -13])
  have hm := merge_left (literal (valuation q) (1464)) (literal (valuation q) (1475)) (countLit q [-2, -4, -6]) (countLit q [-8, -10, -12, -13]) (count1474 q) 2 (meaning1464 q) (meaning1475 q) hs
  change valuation q 1464 = false ∨ valuation q 1475 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause960 (q : Snake 81) (h : Conditions q) : valuation q 1464 = false ∨ valuation q 1470 = false ∨ valuation q 1476 = true := by
  have hs : count1474 q = (countLit q [-2, -4, -6]) + (countLit q [-8, -10, -12, -13]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-2, -4, -6]) (l₂ := [-8, -10, -12, -13])
  have hm := merge_two (literal (valuation q) (1464)) (literal (valuation q) (1470)) (literal (valuation q) (1476)) (countLit q [-2, -4, -6]) (countLit q [-8, -10, -12, -13]) (count1474 q) 2 1 (meaning1464 q) (meaning1470 q) (meaning1476 q) hs
  change valuation q 1464 = false ∨ valuation q 1470 = false ∨ valuation q 1476 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem block29 (q : Snake 81) (h : Conditions q) : Dfs112FirstBoolean.Block29 (valuation q) :=
  ⟨clause929 q h, clause930 q h, clause931 q h, clause932 q h, clause933 q h, clause934 q h, clause935 q h, clause936 q h, clause937 q h, clause938 q h, clause939 q h, clause940 q h, clause941 q h, clause942 q h, clause943 q h, clause944 q h, clause945 q h, clause946 q h, clause947 q h, clause948 q h, clause949 q h, clause950 q h, clause951 q h, clause952 q h, clause953 q h, clause954 q h, clause955 q h, clause956 q h, clause957 q h, clause958 q h, clause959 q h, clause960 q h⟩

end
end Snake9.Regrowth.First112
