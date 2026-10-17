import E112027Semantics
import B112E027Inputs
namespace Snake9.Regrowth.E112027
noncomputable section
local instance blockDec29 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause929 (q : Nat → Bool) : valuationOf q 1437 = false ∨ valuationOf q 1439 = true := by
  have hs : count1439 q = (countLit q [-2]) + (countLit q [-3, -7]) := List.countP_append (p := literal q) (l₁ := [-2]) (l₂ := [-3, -7])
  have hm := merge_right (literal (valuationOf q) (1437)) (literal (valuationOf q) (1439)) (countLit q [-2]) (countLit q [-3, -7]) (count1439 q) 1 (meaning1437 q) (meaning1439 q) hs
  change valuationOf q 1437 = false ∨ valuationOf q 1439 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause929 (q : Snake 81) (h : Conditions q) : valuation q 1437 = false ∨ valuation q 1439 = true := counterClause929 (baseVal q)

theorem counterClause930 (q : Nat → Bool) : valuationOf q 1438 = false ∨ valuationOf q 1440 = true := by
  have hs : count1439 q = (countLit q [-2]) + (countLit q [-3, -7]) := List.countP_append (p := literal q) (l₁ := [-2]) (l₂ := [-3, -7])
  have hm := merge_right (literal (valuationOf q) (1438)) (literal (valuationOf q) (1440)) (countLit q [-2]) (countLit q [-3, -7]) (count1439 q) 2 (meaning1438 q) (meaning1440 q) hs
  change valuationOf q 1438 = false ∨ valuationOf q 1440 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause930 (q : Snake 81) (h : Conditions q) : valuation q 1438 = false ∨ valuation q 1440 = true := counterClause930 (baseVal q)

theorem counterClause931 (q : Nat → Bool) : valuationOf q 2 = true ∨ valuationOf q 1439 = true := by
  have hs : count1439 q = (countLit q [-2]) + (countLit q [-3, -7]) := List.countP_append (p := literal q) (l₁ := [-2]) (l₂ := [-3, -7])
  have hm := merge_left (literal (valuationOf q) (-2)) (literal (valuationOf q) (1439)) (countLit q [-2]) (countLit q [-3, -7]) (count1439 q) 1 (meaningNeg2 q) (meaning1439 q) hs
  change (! (valuationOf q 2)) = false ∨ valuationOf q 1439 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause931 (q : Snake 81) (h : Conditions q) : valuation q 2 = true ∨ valuation q 1439 = true := counterClause931 (baseVal q)

theorem counterClause932 (q : Nat → Bool) : valuationOf q 2 = true ∨ valuationOf q 1437 = false ∨ valuationOf q 1440 = true := by
  have hs : count1439 q = (countLit q [-2]) + (countLit q [-3, -7]) := List.countP_append (p := literal q) (l₁ := [-2]) (l₂ := [-3, -7])
  have hm := merge_two (literal (valuationOf q) (-2)) (literal (valuationOf q) (1437)) (literal (valuationOf q) (1440)) (countLit q [-2]) (countLit q [-3, -7]) (count1439 q) 1 1 (meaningNeg2 q) (meaning1437 q) (meaning1440 q) hs
  change (! (valuationOf q 2)) = false ∨ valuationOf q 1437 = false ∨ valuationOf q 1440 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause932 (q : Snake 81) (h : Conditions q) : valuation q 2 = true ∨ valuation q 1437 = false ∨ valuation q 1440 = true := counterClause932 (baseVal q)

theorem counterClause933 (q : Nat → Bool) : valuationOf q 2 = true ∨ valuationOf q 1438 = false ∨ valuationOf q 1441 = true := by
  have hs : count1439 q = (countLit q [-2]) + (countLit q [-3, -7]) := List.countP_append (p := literal q) (l₁ := [-2]) (l₂ := [-3, -7])
  have hm := merge_two (literal (valuationOf q) (-2)) (literal (valuationOf q) (1438)) (literal (valuationOf q) (1441)) (countLit q [-2]) (countLit q [-3, -7]) (count1439 q) 1 2 (meaningNeg2 q) (meaning1438 q) (meaning1441 q) hs
  change (! (valuationOf q 2)) = false ∨ valuationOf q 1438 = false ∨ valuationOf q 1441 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause933 (q : Snake 81) (h : Conditions q) : valuation q 2 = true ∨ valuation q 1438 = false ∨ valuation q 1441 = true := counterClause933 (baseVal q)

theorem counterClause934 (q : Nat → Bool) : valuationOf q 11 = true ∨ valuationOf q 1442 = true := by
  have hs : count1442 q = (countLit q [-8]) + (countLit q [-11]) := List.countP_append (p := literal q) (l₁ := [-8]) (l₂ := [-11])
  have hm := merge_right (literal (valuationOf q) (-11)) (literal (valuationOf q) (1442)) (countLit q [-8]) (countLit q [-11]) (count1442 q) 1 (meaningNeg11 q) (meaning1442 q) hs
  change (! (valuationOf q 11)) = false ∨ valuationOf q 1442 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause934 (q : Snake 81) (h : Conditions q) : valuation q 11 = true ∨ valuation q 1442 = true := counterClause934 (baseVal q)

theorem counterClause935 (q : Nat → Bool) : valuationOf q 8 = true ∨ valuationOf q 1442 = true := by
  have hs : count1442 q = (countLit q [-8]) + (countLit q [-11]) := List.countP_append (p := literal q) (l₁ := [-8]) (l₂ := [-11])
  have hm := merge_left (literal (valuationOf q) (-8)) (literal (valuationOf q) (1442)) (countLit q [-8]) (countLit q [-11]) (count1442 q) 1 (meaningNeg8 q) (meaning1442 q) hs
  change (! (valuationOf q 8)) = false ∨ valuationOf q 1442 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause935 (q : Snake 81) (h : Conditions q) : valuation q 8 = true ∨ valuation q 1442 = true := counterClause935 (baseVal q)

theorem counterClause936 (q : Nat → Bool) : valuationOf q 8 = true ∨ valuationOf q 11 = true ∨ valuationOf q 1443 = true := by
  have hs : count1442 q = (countLit q [-8]) + (countLit q [-11]) := List.countP_append (p := literal q) (l₁ := [-8]) (l₂ := [-11])
  have hm := merge_two (literal (valuationOf q) (-8)) (literal (valuationOf q) (-11)) (literal (valuationOf q) (1443)) (countLit q [-8]) (countLit q [-11]) (count1442 q) 1 1 (meaningNeg8 q) (meaningNeg11 q) (meaning1443 q) hs
  change (! (valuationOf q 8)) = false ∨ (! (valuationOf q 11)) = false ∨ valuationOf q 1443 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause936 (q : Snake 81) (h : Conditions q) : valuation q 8 = true ∨ valuation q 11 = true ∨ valuation q 1443 = true := counterClause936 (baseVal q)

theorem counterClause937 (q : Nat → Bool) : valuationOf q 15 = true ∨ valuationOf q 1444 = true := by
  have hs : count1444 q = (countLit q [-13]) + (countLit q [-15]) := List.countP_append (p := literal q) (l₁ := [-13]) (l₂ := [-15])
  have hm := merge_right (literal (valuationOf q) (-15)) (literal (valuationOf q) (1444)) (countLit q [-13]) (countLit q [-15]) (count1444 q) 1 (meaningNeg15 q) (meaning1444 q) hs
  change (! (valuationOf q 15)) = false ∨ valuationOf q 1444 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause937 (q : Snake 81) (h : Conditions q) : valuation q 15 = true ∨ valuation q 1444 = true := counterClause937 (baseVal q)

theorem counterClause938 (q : Nat → Bool) : valuationOf q 13 = true ∨ valuationOf q 1444 = true := by
  have hs : count1444 q = (countLit q [-13]) + (countLit q [-15]) := List.countP_append (p := literal q) (l₁ := [-13]) (l₂ := [-15])
  have hm := merge_left (literal (valuationOf q) (-13)) (literal (valuationOf q) (1444)) (countLit q [-13]) (countLit q [-15]) (count1444 q) 1 (meaningNeg13 q) (meaning1444 q) hs
  change (! (valuationOf q 13)) = false ∨ valuationOf q 1444 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause938 (q : Snake 81) (h : Conditions q) : valuation q 13 = true ∨ valuation q 1444 = true := counterClause938 (baseVal q)

theorem counterClause939 (q : Nat → Bool) : valuationOf q 13 = true ∨ valuationOf q 15 = true ∨ valuationOf q 1445 = true := by
  have hs : count1444 q = (countLit q [-13]) + (countLit q [-15]) := List.countP_append (p := literal q) (l₁ := [-13]) (l₂ := [-15])
  have hm := merge_two (literal (valuationOf q) (-13)) (literal (valuationOf q) (-15)) (literal (valuationOf q) (1445)) (countLit q [-13]) (countLit q [-15]) (count1444 q) 1 1 (meaningNeg13 q) (meaningNeg15 q) (meaning1445 q) hs
  change (! (valuationOf q 13)) = false ∨ (! (valuationOf q 15)) = false ∨ valuationOf q 1445 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause939 (q : Snake 81) (h : Conditions q) : valuation q 13 = true ∨ valuation q 15 = true ∨ valuation q 1445 = true := counterClause939 (baseVal q)

theorem counterClause940 (q : Nat → Bool) : valuationOf q 1444 = false ∨ valuationOf q 1446 = true := by
  have hs : count1446 q = (countLit q [-8, -11]) + (countLit q [-13, -15]) := List.countP_append (p := literal q) (l₁ := [-8, -11]) (l₂ := [-13, -15])
  have hm := merge_right (literal (valuationOf q) (1444)) (literal (valuationOf q) (1446)) (countLit q [-8, -11]) (countLit q [-13, -15]) (count1446 q) 1 (meaning1444 q) (meaning1446 q) hs
  change valuationOf q 1444 = false ∨ valuationOf q 1446 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause940 (q : Snake 81) (h : Conditions q) : valuation q 1444 = false ∨ valuation q 1446 = true := counterClause940 (baseVal q)

theorem counterClause941 (q : Nat → Bool) : valuationOf q 1445 = false ∨ valuationOf q 1447 = true := by
  have hs : count1446 q = (countLit q [-8, -11]) + (countLit q [-13, -15]) := List.countP_append (p := literal q) (l₁ := [-8, -11]) (l₂ := [-13, -15])
  have hm := merge_right (literal (valuationOf q) (1445)) (literal (valuationOf q) (1447)) (countLit q [-8, -11]) (countLit q [-13, -15]) (count1446 q) 2 (meaning1445 q) (meaning1447 q) hs
  change valuationOf q 1445 = false ∨ valuationOf q 1447 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause941 (q : Snake 81) (h : Conditions q) : valuation q 1445 = false ∨ valuation q 1447 = true := counterClause941 (baseVal q)

theorem counterClause942 (q : Nat → Bool) : valuationOf q 1442 = false ∨ valuationOf q 1446 = true := by
  have hs : count1446 q = (countLit q [-8, -11]) + (countLit q [-13, -15]) := List.countP_append (p := literal q) (l₁ := [-8, -11]) (l₂ := [-13, -15])
  have hm := merge_left (literal (valuationOf q) (1442)) (literal (valuationOf q) (1446)) (countLit q [-8, -11]) (countLit q [-13, -15]) (count1446 q) 1 (meaning1442 q) (meaning1446 q) hs
  change valuationOf q 1442 = false ∨ valuationOf q 1446 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause942 (q : Snake 81) (h : Conditions q) : valuation q 1442 = false ∨ valuation q 1446 = true := counterClause942 (baseVal q)

theorem counterClause943 (q : Nat → Bool) : valuationOf q 1442 = false ∨ valuationOf q 1444 = false ∨ valuationOf q 1447 = true := by
  have hs : count1446 q = (countLit q [-8, -11]) + (countLit q [-13, -15]) := List.countP_append (p := literal q) (l₁ := [-8, -11]) (l₂ := [-13, -15])
  have hm := merge_two (literal (valuationOf q) (1442)) (literal (valuationOf q) (1444)) (literal (valuationOf q) (1447)) (countLit q [-8, -11]) (countLit q [-13, -15]) (count1446 q) 1 1 (meaning1442 q) (meaning1444 q) (meaning1447 q) hs
  change valuationOf q 1442 = false ∨ valuationOf q 1444 = false ∨ valuationOf q 1447 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause943 (q : Snake 81) (h : Conditions q) : valuation q 1442 = false ∨ valuation q 1444 = false ∨ valuation q 1447 = true := counterClause943 (baseVal q)

theorem counterClause944 (q : Nat → Bool) : valuationOf q 1442 = false ∨ valuationOf q 1445 = false ∨ valuationOf q 1448 = true := by
  have hs : count1446 q = (countLit q [-8, -11]) + (countLit q [-13, -15]) := List.countP_append (p := literal q) (l₁ := [-8, -11]) (l₂ := [-13, -15])
  have hm := merge_two (literal (valuationOf q) (1442)) (literal (valuationOf q) (1445)) (literal (valuationOf q) (1448)) (countLit q [-8, -11]) (countLit q [-13, -15]) (count1446 q) 1 2 (meaning1442 q) (meaning1445 q) (meaning1448 q) hs
  change valuationOf q 1442 = false ∨ valuationOf q 1445 = false ∨ valuationOf q 1448 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause944 (q : Snake 81) (h : Conditions q) : valuation q 1442 = false ∨ valuation q 1445 = false ∨ valuation q 1448 = true := counterClause944 (baseVal q)

theorem counterClause945 (q : Nat → Bool) : valuationOf q 1443 = false ∨ valuationOf q 1447 = true := by
  have hs : count1446 q = (countLit q [-8, -11]) + (countLit q [-13, -15]) := List.countP_append (p := literal q) (l₁ := [-8, -11]) (l₂ := [-13, -15])
  have hm := merge_left (literal (valuationOf q) (1443)) (literal (valuationOf q) (1447)) (countLit q [-8, -11]) (countLit q [-13, -15]) (count1446 q) 2 (meaning1443 q) (meaning1447 q) hs
  change valuationOf q 1443 = false ∨ valuationOf q 1447 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause945 (q : Snake 81) (h : Conditions q) : valuation q 1443 = false ∨ valuation q 1447 = true := counterClause945 (baseVal q)

theorem counterClause946 (q : Nat → Bool) : valuationOf q 1443 = false ∨ valuationOf q 1444 = false ∨ valuationOf q 1448 = true := by
  have hs : count1446 q = (countLit q [-8, -11]) + (countLit q [-13, -15]) := List.countP_append (p := literal q) (l₁ := [-8, -11]) (l₂ := [-13, -15])
  have hm := merge_two (literal (valuationOf q) (1443)) (literal (valuationOf q) (1444)) (literal (valuationOf q) (1448)) (countLit q [-8, -11]) (countLit q [-13, -15]) (count1446 q) 2 1 (meaning1443 q) (meaning1444 q) (meaning1448 q) hs
  change valuationOf q 1443 = false ∨ valuationOf q 1444 = false ∨ valuationOf q 1448 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause946 (q : Snake 81) (h : Conditions q) : valuation q 1443 = false ∨ valuation q 1444 = false ∨ valuation q 1448 = true := counterClause946 (baseVal q)

theorem counterClause947 (q : Nat → Bool) : valuationOf q 1443 = false ∨ valuationOf q 1445 = false ∨ valuationOf q 1449 = true := by
  have hs : count1446 q = (countLit q [-8, -11]) + (countLit q [-13, -15]) := List.countP_append (p := literal q) (l₁ := [-8, -11]) (l₂ := [-13, -15])
  have hm := merge_two (literal (valuationOf q) (1443)) (literal (valuationOf q) (1445)) (literal (valuationOf q) (1449)) (countLit q [-8, -11]) (countLit q [-13, -15]) (count1446 q) 2 2 (meaning1443 q) (meaning1445 q) (meaning1449 q) hs
  change valuationOf q 1443 = false ∨ valuationOf q 1445 = false ∨ valuationOf q 1449 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause947 (q : Snake 81) (h : Conditions q) : valuation q 1443 = false ∨ valuation q 1445 = false ∨ valuation q 1449 = true := counterClause947 (baseVal q)

theorem counterClause948 (q : Nat → Bool) : valuationOf q 1446 = false ∨ valuationOf q 1450 = true := by
  have hs : count1450 q = (countLit q [-2, -3, -7]) + (countLit q [-8, -11, -13, -15]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -7]) (l₂ := [-8, -11, -13, -15])
  have hm := merge_right (literal (valuationOf q) (1446)) (literal (valuationOf q) (1450)) (countLit q [-2, -3, -7]) (countLit q [-8, -11, -13, -15]) (count1450 q) 1 (meaning1446 q) (meaning1450 q) hs
  change valuationOf q 1446 = false ∨ valuationOf q 1450 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause948 (q : Snake 81) (h : Conditions q) : valuation q 1446 = false ∨ valuation q 1450 = true := counterClause948 (baseVal q)

theorem counterClause949 (q : Nat → Bool) : valuationOf q 1447 = false ∨ valuationOf q 1451 = true := by
  have hs : count1450 q = (countLit q [-2, -3, -7]) + (countLit q [-8, -11, -13, -15]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -7]) (l₂ := [-8, -11, -13, -15])
  have hm := merge_right (literal (valuationOf q) (1447)) (literal (valuationOf q) (1451)) (countLit q [-2, -3, -7]) (countLit q [-8, -11, -13, -15]) (count1450 q) 2 (meaning1447 q) (meaning1451 q) hs
  change valuationOf q 1447 = false ∨ valuationOf q 1451 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause949 (q : Snake 81) (h : Conditions q) : valuation q 1447 = false ∨ valuation q 1451 = true := counterClause949 (baseVal q)

theorem counterClause950 (q : Nat → Bool) : valuationOf q 1448 = false ∨ valuationOf q 1452 = true := by
  have hs : count1450 q = (countLit q [-2, -3, -7]) + (countLit q [-8, -11, -13, -15]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -7]) (l₂ := [-8, -11, -13, -15])
  have hm := merge_right (literal (valuationOf q) (1448)) (literal (valuationOf q) (1452)) (countLit q [-2, -3, -7]) (countLit q [-8, -11, -13, -15]) (count1450 q) 3 (meaning1448 q) (meaning1452 q) hs
  change valuationOf q 1448 = false ∨ valuationOf q 1452 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause950 (q : Snake 81) (h : Conditions q) : valuation q 1448 = false ∨ valuation q 1452 = true := counterClause950 (baseVal q)

theorem counterClause951 (q : Nat → Bool) : valuationOf q 1449 = false ∨ valuationOf q 1453 = true := by
  have hs : count1450 q = (countLit q [-2, -3, -7]) + (countLit q [-8, -11, -13, -15]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -7]) (l₂ := [-8, -11, -13, -15])
  have hm := merge_right (literal (valuationOf q) (1449)) (literal (valuationOf q) (1453)) (countLit q [-2, -3, -7]) (countLit q [-8, -11, -13, -15]) (count1450 q) 4 (meaning1449 q) (meaning1453 q) hs
  change valuationOf q 1449 = false ∨ valuationOf q 1453 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause951 (q : Snake 81) (h : Conditions q) : valuation q 1449 = false ∨ valuation q 1453 = true := counterClause951 (baseVal q)

theorem counterClause952 (q : Nat → Bool) : valuationOf q 1439 = false ∨ valuationOf q 1450 = true := by
  have hs : count1450 q = (countLit q [-2, -3, -7]) + (countLit q [-8, -11, -13, -15]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -7]) (l₂ := [-8, -11, -13, -15])
  have hm := merge_left (literal (valuationOf q) (1439)) (literal (valuationOf q) (1450)) (countLit q [-2, -3, -7]) (countLit q [-8, -11, -13, -15]) (count1450 q) 1 (meaning1439 q) (meaning1450 q) hs
  change valuationOf q 1439 = false ∨ valuationOf q 1450 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause952 (q : Snake 81) (h : Conditions q) : valuation q 1439 = false ∨ valuation q 1450 = true := counterClause952 (baseVal q)

theorem counterClause953 (q : Nat → Bool) : valuationOf q 1439 = false ∨ valuationOf q 1446 = false ∨ valuationOf q 1451 = true := by
  have hs : count1450 q = (countLit q [-2, -3, -7]) + (countLit q [-8, -11, -13, -15]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -7]) (l₂ := [-8, -11, -13, -15])
  have hm := merge_two (literal (valuationOf q) (1439)) (literal (valuationOf q) (1446)) (literal (valuationOf q) (1451)) (countLit q [-2, -3, -7]) (countLit q [-8, -11, -13, -15]) (count1450 q) 1 1 (meaning1439 q) (meaning1446 q) (meaning1451 q) hs
  change valuationOf q 1439 = false ∨ valuationOf q 1446 = false ∨ valuationOf q 1451 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause953 (q : Snake 81) (h : Conditions q) : valuation q 1439 = false ∨ valuation q 1446 = false ∨ valuation q 1451 = true := counterClause953 (baseVal q)

theorem counterClause954 (q : Nat → Bool) : valuationOf q 1439 = false ∨ valuationOf q 1447 = false ∨ valuationOf q 1452 = true := by
  have hs : count1450 q = (countLit q [-2, -3, -7]) + (countLit q [-8, -11, -13, -15]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -7]) (l₂ := [-8, -11, -13, -15])
  have hm := merge_two (literal (valuationOf q) (1439)) (literal (valuationOf q) (1447)) (literal (valuationOf q) (1452)) (countLit q [-2, -3, -7]) (countLit q [-8, -11, -13, -15]) (count1450 q) 1 2 (meaning1439 q) (meaning1447 q) (meaning1452 q) hs
  change valuationOf q 1439 = false ∨ valuationOf q 1447 = false ∨ valuationOf q 1452 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause954 (q : Snake 81) (h : Conditions q) : valuation q 1439 = false ∨ valuation q 1447 = false ∨ valuation q 1452 = true := counterClause954 (baseVal q)

theorem counterClause955 (q : Nat → Bool) : valuationOf q 1439 = false ∨ valuationOf q 1448 = false ∨ valuationOf q 1453 = true := by
  have hs : count1450 q = (countLit q [-2, -3, -7]) + (countLit q [-8, -11, -13, -15]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -7]) (l₂ := [-8, -11, -13, -15])
  have hm := merge_two (literal (valuationOf q) (1439)) (literal (valuationOf q) (1448)) (literal (valuationOf q) (1453)) (countLit q [-2, -3, -7]) (countLit q [-8, -11, -13, -15]) (count1450 q) 1 3 (meaning1439 q) (meaning1448 q) (meaning1453 q) hs
  change valuationOf q 1439 = false ∨ valuationOf q 1448 = false ∨ valuationOf q 1453 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause955 (q : Snake 81) (h : Conditions q) : valuation q 1439 = false ∨ valuation q 1448 = false ∨ valuation q 1453 = true := counterClause955 (baseVal q)

theorem counterClause956 (q : Nat → Bool) : valuationOf q 1439 = false ∨ valuationOf q 1449 = false ∨ valuationOf q 1454 = true := by
  have hs : count1450 q = (countLit q [-2, -3, -7]) + (countLit q [-8, -11, -13, -15]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -7]) (l₂ := [-8, -11, -13, -15])
  have hm := merge_two (literal (valuationOf q) (1439)) (literal (valuationOf q) (1449)) (literal (valuationOf q) (1454)) (countLit q [-2, -3, -7]) (countLit q [-8, -11, -13, -15]) (count1450 q) 1 4 (meaning1439 q) (meaning1449 q) (meaning1454 q) hs
  change valuationOf q 1439 = false ∨ valuationOf q 1449 = false ∨ valuationOf q 1454 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause956 (q : Snake 81) (h : Conditions q) : valuation q 1439 = false ∨ valuation q 1449 = false ∨ valuation q 1454 = true := counterClause956 (baseVal q)

theorem counterClause957 (q : Nat → Bool) : valuationOf q 1440 = false ∨ valuationOf q 1451 = true := by
  have hs : count1450 q = (countLit q [-2, -3, -7]) + (countLit q [-8, -11, -13, -15]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -7]) (l₂ := [-8, -11, -13, -15])
  have hm := merge_left (literal (valuationOf q) (1440)) (literal (valuationOf q) (1451)) (countLit q [-2, -3, -7]) (countLit q [-8, -11, -13, -15]) (count1450 q) 2 (meaning1440 q) (meaning1451 q) hs
  change valuationOf q 1440 = false ∨ valuationOf q 1451 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause957 (q : Snake 81) (h : Conditions q) : valuation q 1440 = false ∨ valuation q 1451 = true := counterClause957 (baseVal q)

theorem counterClause958 (q : Nat → Bool) : valuationOf q 1440 = false ∨ valuationOf q 1446 = false ∨ valuationOf q 1452 = true := by
  have hs : count1450 q = (countLit q [-2, -3, -7]) + (countLit q [-8, -11, -13, -15]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -7]) (l₂ := [-8, -11, -13, -15])
  have hm := merge_two (literal (valuationOf q) (1440)) (literal (valuationOf q) (1446)) (literal (valuationOf q) (1452)) (countLit q [-2, -3, -7]) (countLit q [-8, -11, -13, -15]) (count1450 q) 2 1 (meaning1440 q) (meaning1446 q) (meaning1452 q) hs
  change valuationOf q 1440 = false ∨ valuationOf q 1446 = false ∨ valuationOf q 1452 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause958 (q : Snake 81) (h : Conditions q) : valuation q 1440 = false ∨ valuation q 1446 = false ∨ valuation q 1452 = true := counterClause958 (baseVal q)

theorem counterClause959 (q : Nat → Bool) : valuationOf q 1440 = false ∨ valuationOf q 1447 = false ∨ valuationOf q 1453 = true := by
  have hs : count1450 q = (countLit q [-2, -3, -7]) + (countLit q [-8, -11, -13, -15]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -7]) (l₂ := [-8, -11, -13, -15])
  have hm := merge_two (literal (valuationOf q) (1440)) (literal (valuationOf q) (1447)) (literal (valuationOf q) (1453)) (countLit q [-2, -3, -7]) (countLit q [-8, -11, -13, -15]) (count1450 q) 2 2 (meaning1440 q) (meaning1447 q) (meaning1453 q) hs
  change valuationOf q 1440 = false ∨ valuationOf q 1447 = false ∨ valuationOf q 1453 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause959 (q : Snake 81) (h : Conditions q) : valuation q 1440 = false ∨ valuation q 1447 = false ∨ valuation q 1453 = true := counterClause959 (baseVal q)

theorem counterClause960 (q : Nat → Bool) : valuationOf q 1440 = false ∨ valuationOf q 1448 = false ∨ valuationOf q 1454 = true := by
  have hs : count1450 q = (countLit q [-2, -3, -7]) + (countLit q [-8, -11, -13, -15]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -7]) (l₂ := [-8, -11, -13, -15])
  have hm := merge_two (literal (valuationOf q) (1440)) (literal (valuationOf q) (1448)) (literal (valuationOf q) (1454)) (countLit q [-2, -3, -7]) (countLit q [-8, -11, -13, -15]) (count1450 q) 2 3 (meaning1440 q) (meaning1448 q) (meaning1454 q) hs
  change valuationOf q 1440 = false ∨ valuationOf q 1448 = false ∨ valuationOf q 1454 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause960 (q : Snake 81) (h : Conditions q) : valuation q 1440 = false ∨ valuation q 1448 = false ∨ valuation q 1454 = true := counterClause960 (baseVal q)

theorem block29 (q : Snake 81) (h : Conditions q) : B112E027.Block29 (valuation q) :=
  ⟨clause929 q h, clause930 q h, clause931 q h, clause932 q h, clause933 q h, clause934 q h, clause935 q h, clause936 q h, clause937 q h, clause938 q h, clause939 q h, clause940 q h, clause941 q h, clause942 q h, clause943 q h, clause944 q h, clause945 q h, clause946 q h, clause947 q h, clause948 q h, clause949 q h, clause950 q h, clause951 q h, clause952 q h, clause953 q h, clause954 q h, clause955 q h, clause956 q h, clause957 q h, clause958 q h, clause959 q h, clause960 q h⟩

end
end Snake9.Regrowth.E112027
