import E112026Semantics
import B112E026Inputs
namespace Snake9.Regrowth.E112026
noncomputable section
local instance blockDec29 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause929 (q : Nat → Bool) : valuationOf q 1460 = false ∨ valuationOf q 1481 = false ∨ valuationOf q 1494 = true := by
  have hs : count1487 q = (countLit q [-1, -3, -5, -6, -8, -10, -11]) + (countLit q [-13, -14, -18, -19, -20, -22, -25, -26]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -5, -6, -8, -10, -11]) (l₂ := [-13, -14, -18, -19, -20, -22, -25, -26])
  have hm := merge_two (literal (valuationOf q) (1460)) (literal (valuationOf q) (1481)) (literal (valuationOf q) (1494)) (countLit q [-1, -3, -5, -6, -8, -10, -11]) (countLit q [-13, -14, -18, -19, -20, -22, -25, -26]) (count1487 q) 5 3 (meaning1460 q) (meaning1481 q) (meaning1494 q) hs
  change valuationOf q 1460 = false ∨ valuationOf q 1481 = false ∨ valuationOf q 1494 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause929 (q : Snake 81) (h : Conditions q) : valuation q 1460 = false ∨ valuation q 1481 = false ∨ valuation q 1494 = true := counterClause929 (baseVal q)

theorem counterClause930 (q : Nat → Bool) : valuationOf q 31 = true ∨ valuationOf q 1502 = true := by
  have hs : count1502 q = (countLit q [-28]) + (countLit q [-31]) := List.countP_append (p := literal q) (l₁ := [-28]) (l₂ := [-31])
  have hm := merge_right (literal (valuationOf q) (-31)) (literal (valuationOf q) (1502)) (countLit q [-28]) (countLit q [-31]) (count1502 q) 1 (meaningNeg31 q) (meaning1502 q) hs
  change (! (valuationOf q 31)) = false ∨ valuationOf q 1502 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause930 (q : Snake 81) (h : Conditions q) : valuation q 31 = true ∨ valuation q 1502 = true := counterClause930 (baseVal q)

theorem counterClause931 (q : Nat → Bool) : valuationOf q 28 = true ∨ valuationOf q 1502 = true := by
  have hs : count1502 q = (countLit q [-28]) + (countLit q [-31]) := List.countP_append (p := literal q) (l₁ := [-28]) (l₂ := [-31])
  have hm := merge_left (literal (valuationOf q) (-28)) (literal (valuationOf q) (1502)) (countLit q [-28]) (countLit q [-31]) (count1502 q) 1 (meaningNeg28 q) (meaning1502 q) hs
  change (! (valuationOf q 28)) = false ∨ valuationOf q 1502 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause931 (q : Snake 81) (h : Conditions q) : valuation q 28 = true ∨ valuation q 1502 = true := counterClause931 (baseVal q)

theorem counterClause932 (q : Nat → Bool) : valuationOf q 28 = true ∨ valuationOf q 31 = true ∨ valuationOf q 1503 = true := by
  have hs : count1502 q = (countLit q [-28]) + (countLit q [-31]) := List.countP_append (p := literal q) (l₁ := [-28]) (l₂ := [-31])
  have hm := merge_two (literal (valuationOf q) (-28)) (literal (valuationOf q) (-31)) (literal (valuationOf q) (1503)) (countLit q [-28]) (countLit q [-31]) (count1502 q) 1 1 (meaningNeg28 q) (meaningNeg31 q) (meaning1503 q) hs
  change (! (valuationOf q 28)) = false ∨ (! (valuationOf q 31)) = false ∨ valuationOf q 1503 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause932 (q : Snake 81) (h : Conditions q) : valuation q 28 = true ∨ valuation q 31 = true ∨ valuation q 1503 = true := counterClause932 (baseVal q)

theorem counterClause933 (q : Nat → Bool) : valuationOf q 35 = true ∨ valuationOf q 1504 = true := by
  have hs : count1504 q = (countLit q [-33]) + (countLit q [-35]) := List.countP_append (p := literal q) (l₁ := [-33]) (l₂ := [-35])
  have hm := merge_right (literal (valuationOf q) (-35)) (literal (valuationOf q) (1504)) (countLit q [-33]) (countLit q [-35]) (count1504 q) 1 (meaningNeg35 q) (meaning1504 q) hs
  change (! (valuationOf q 35)) = false ∨ valuationOf q 1504 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause933 (q : Snake 81) (h : Conditions q) : valuation q 35 = true ∨ valuation q 1504 = true := counterClause933 (baseVal q)

theorem counterClause934 (q : Nat → Bool) : valuationOf q 33 = true ∨ valuationOf q 1504 = true := by
  have hs : count1504 q = (countLit q [-33]) + (countLit q [-35]) := List.countP_append (p := literal q) (l₁ := [-33]) (l₂ := [-35])
  have hm := merge_left (literal (valuationOf q) (-33)) (literal (valuationOf q) (1504)) (countLit q [-33]) (countLit q [-35]) (count1504 q) 1 (meaningNeg33 q) (meaning1504 q) hs
  change (! (valuationOf q 33)) = false ∨ valuationOf q 1504 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause934 (q : Snake 81) (h : Conditions q) : valuation q 33 = true ∨ valuation q 1504 = true := counterClause934 (baseVal q)

theorem counterClause935 (q : Nat → Bool) : valuationOf q 33 = true ∨ valuationOf q 35 = true ∨ valuationOf q 1505 = true := by
  have hs : count1504 q = (countLit q [-33]) + (countLit q [-35]) := List.countP_append (p := literal q) (l₁ := [-33]) (l₂ := [-35])
  have hm := merge_two (literal (valuationOf q) (-33)) (literal (valuationOf q) (-35)) (literal (valuationOf q) (1505)) (countLit q [-33]) (countLit q [-35]) (count1504 q) 1 1 (meaningNeg33 q) (meaningNeg35 q) (meaning1505 q) hs
  change (! (valuationOf q 33)) = false ∨ (! (valuationOf q 35)) = false ∨ valuationOf q 1505 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause935 (q : Snake 81) (h : Conditions q) : valuation q 33 = true ∨ valuation q 35 = true ∨ valuation q 1505 = true := counterClause935 (baseVal q)

theorem counterClause936 (q : Nat → Bool) : valuationOf q 1504 = false ∨ valuationOf q 1506 = true := by
  have hs : count1506 q = (countLit q [-28, -31]) + (countLit q [-33, -35]) := List.countP_append (p := literal q) (l₁ := [-28, -31]) (l₂ := [-33, -35])
  have hm := merge_right (literal (valuationOf q) (1504)) (literal (valuationOf q) (1506)) (countLit q [-28, -31]) (countLit q [-33, -35]) (count1506 q) 1 (meaning1504 q) (meaning1506 q) hs
  change valuationOf q 1504 = false ∨ valuationOf q 1506 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause936 (q : Snake 81) (h : Conditions q) : valuation q 1504 = false ∨ valuation q 1506 = true := counterClause936 (baseVal q)

theorem counterClause937 (q : Nat → Bool) : valuationOf q 1505 = false ∨ valuationOf q 1507 = true := by
  have hs : count1506 q = (countLit q [-28, -31]) + (countLit q [-33, -35]) := List.countP_append (p := literal q) (l₁ := [-28, -31]) (l₂ := [-33, -35])
  have hm := merge_right (literal (valuationOf q) (1505)) (literal (valuationOf q) (1507)) (countLit q [-28, -31]) (countLit q [-33, -35]) (count1506 q) 2 (meaning1505 q) (meaning1507 q) hs
  change valuationOf q 1505 = false ∨ valuationOf q 1507 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause937 (q : Snake 81) (h : Conditions q) : valuation q 1505 = false ∨ valuation q 1507 = true := counterClause937 (baseVal q)

theorem counterClause938 (q : Nat → Bool) : valuationOf q 1502 = false ∨ valuationOf q 1506 = true := by
  have hs : count1506 q = (countLit q [-28, -31]) + (countLit q [-33, -35]) := List.countP_append (p := literal q) (l₁ := [-28, -31]) (l₂ := [-33, -35])
  have hm := merge_left (literal (valuationOf q) (1502)) (literal (valuationOf q) (1506)) (countLit q [-28, -31]) (countLit q [-33, -35]) (count1506 q) 1 (meaning1502 q) (meaning1506 q) hs
  change valuationOf q 1502 = false ∨ valuationOf q 1506 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause938 (q : Snake 81) (h : Conditions q) : valuation q 1502 = false ∨ valuation q 1506 = true := counterClause938 (baseVal q)

theorem counterClause939 (q : Nat → Bool) : valuationOf q 1502 = false ∨ valuationOf q 1504 = false ∨ valuationOf q 1507 = true := by
  have hs : count1506 q = (countLit q [-28, -31]) + (countLit q [-33, -35]) := List.countP_append (p := literal q) (l₁ := [-28, -31]) (l₂ := [-33, -35])
  have hm := merge_two (literal (valuationOf q) (1502)) (literal (valuationOf q) (1504)) (literal (valuationOf q) (1507)) (countLit q [-28, -31]) (countLit q [-33, -35]) (count1506 q) 1 1 (meaning1502 q) (meaning1504 q) (meaning1507 q) hs
  change valuationOf q 1502 = false ∨ valuationOf q 1504 = false ∨ valuationOf q 1507 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause939 (q : Snake 81) (h : Conditions q) : valuation q 1502 = false ∨ valuation q 1504 = false ∨ valuation q 1507 = true := counterClause939 (baseVal q)

theorem counterClause940 (q : Nat → Bool) : valuationOf q 1502 = false ∨ valuationOf q 1505 = false ∨ valuationOf q 1508 = true := by
  have hs : count1506 q = (countLit q [-28, -31]) + (countLit q [-33, -35]) := List.countP_append (p := literal q) (l₁ := [-28, -31]) (l₂ := [-33, -35])
  have hm := merge_two (literal (valuationOf q) (1502)) (literal (valuationOf q) (1505)) (literal (valuationOf q) (1508)) (countLit q [-28, -31]) (countLit q [-33, -35]) (count1506 q) 1 2 (meaning1502 q) (meaning1505 q) (meaning1508 q) hs
  change valuationOf q 1502 = false ∨ valuationOf q 1505 = false ∨ valuationOf q 1508 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause940 (q : Snake 81) (h : Conditions q) : valuation q 1502 = false ∨ valuation q 1505 = false ∨ valuation q 1508 = true := counterClause940 (baseVal q)

theorem counterClause941 (q : Nat → Bool) : valuationOf q 1503 = false ∨ valuationOf q 1507 = true := by
  have hs : count1506 q = (countLit q [-28, -31]) + (countLit q [-33, -35]) := List.countP_append (p := literal q) (l₁ := [-28, -31]) (l₂ := [-33, -35])
  have hm := merge_left (literal (valuationOf q) (1503)) (literal (valuationOf q) (1507)) (countLit q [-28, -31]) (countLit q [-33, -35]) (count1506 q) 2 (meaning1503 q) (meaning1507 q) hs
  change valuationOf q 1503 = false ∨ valuationOf q 1507 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause941 (q : Snake 81) (h : Conditions q) : valuation q 1503 = false ∨ valuation q 1507 = true := counterClause941 (baseVal q)

theorem counterClause942 (q : Nat → Bool) : valuationOf q 1503 = false ∨ valuationOf q 1504 = false ∨ valuationOf q 1508 = true := by
  have hs : count1506 q = (countLit q [-28, -31]) + (countLit q [-33, -35]) := List.countP_append (p := literal q) (l₁ := [-28, -31]) (l₂ := [-33, -35])
  have hm := merge_two (literal (valuationOf q) (1503)) (literal (valuationOf q) (1504)) (literal (valuationOf q) (1508)) (countLit q [-28, -31]) (countLit q [-33, -35]) (count1506 q) 2 1 (meaning1503 q) (meaning1504 q) (meaning1508 q) hs
  change valuationOf q 1503 = false ∨ valuationOf q 1504 = false ∨ valuationOf q 1508 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause942 (q : Snake 81) (h : Conditions q) : valuation q 1503 = false ∨ valuation q 1504 = false ∨ valuation q 1508 = true := counterClause942 (baseVal q)

theorem counterClause943 (q : Nat → Bool) : valuationOf q 1503 = false ∨ valuationOf q 1505 = false ∨ valuationOf q 1509 = true := by
  have hs : count1506 q = (countLit q [-28, -31]) + (countLit q [-33, -35]) := List.countP_append (p := literal q) (l₁ := [-28, -31]) (l₂ := [-33, -35])
  have hm := merge_two (literal (valuationOf q) (1503)) (literal (valuationOf q) (1505)) (literal (valuationOf q) (1509)) (countLit q [-28, -31]) (countLit q [-33, -35]) (count1506 q) 2 2 (meaning1503 q) (meaning1505 q) (meaning1509 q) hs
  change valuationOf q 1503 = false ∨ valuationOf q 1505 = false ∨ valuationOf q 1509 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause943 (q : Snake 81) (h : Conditions q) : valuation q 1503 = false ∨ valuation q 1505 = false ∨ valuation q 1509 = true := counterClause943 (baseVal q)

theorem counterClause944 (q : Nat → Bool) : valuationOf q 37 = true ∨ valuationOf q 1510 = true := by
  have hs : count1510 q = (countLit q [-36]) + (countLit q [-37]) := List.countP_append (p := literal q) (l₁ := [-36]) (l₂ := [-37])
  have hm := merge_right (literal (valuationOf q) (-37)) (literal (valuationOf q) (1510)) (countLit q [-36]) (countLit q [-37]) (count1510 q) 1 (meaningNeg37 q) (meaning1510 q) hs
  change (! (valuationOf q 37)) = false ∨ valuationOf q 1510 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause944 (q : Snake 81) (h : Conditions q) : valuation q 37 = true ∨ valuation q 1510 = true := counterClause944 (baseVal q)

theorem counterClause945 (q : Nat → Bool) : valuationOf q 36 = true ∨ valuationOf q 1510 = true := by
  have hs : count1510 q = (countLit q [-36]) + (countLit q [-37]) := List.countP_append (p := literal q) (l₁ := [-36]) (l₂ := [-37])
  have hm := merge_left (literal (valuationOf q) (-36)) (literal (valuationOf q) (1510)) (countLit q [-36]) (countLit q [-37]) (count1510 q) 1 (meaningNeg36 q) (meaning1510 q) hs
  change (! (valuationOf q 36)) = false ∨ valuationOf q 1510 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause945 (q : Snake 81) (h : Conditions q) : valuation q 36 = true ∨ valuation q 1510 = true := counterClause945 (baseVal q)

theorem counterClause946 (q : Nat → Bool) : valuationOf q 36 = true ∨ valuationOf q 37 = true ∨ valuationOf q 1511 = true := by
  have hs : count1510 q = (countLit q [-36]) + (countLit q [-37]) := List.countP_append (p := literal q) (l₁ := [-36]) (l₂ := [-37])
  have hm := merge_two (literal (valuationOf q) (-36)) (literal (valuationOf q) (-37)) (literal (valuationOf q) (1511)) (countLit q [-36]) (countLit q [-37]) (count1510 q) 1 1 (meaningNeg36 q) (meaningNeg37 q) (meaning1511 q) hs
  change (! (valuationOf q 36)) = false ∨ (! (valuationOf q 37)) = false ∨ valuationOf q 1511 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause946 (q : Snake 81) (h : Conditions q) : valuation q 36 = true ∨ valuation q 37 = true ∨ valuation q 1511 = true := counterClause946 (baseVal q)

theorem counterClause947 (q : Nat → Bool) : valuationOf q 41 = true ∨ valuationOf q 1512 = true := by
  have hs : count1512 q = (countLit q [-39]) + (countLit q [-41]) := List.countP_append (p := literal q) (l₁ := [-39]) (l₂ := [-41])
  have hm := merge_right (literal (valuationOf q) (-41)) (literal (valuationOf q) (1512)) (countLit q [-39]) (countLit q [-41]) (count1512 q) 1 (meaningNeg41 q) (meaning1512 q) hs
  change (! (valuationOf q 41)) = false ∨ valuationOf q 1512 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause947 (q : Snake 81) (h : Conditions q) : valuation q 41 = true ∨ valuation q 1512 = true := counterClause947 (baseVal q)

theorem counterClause948 (q : Nat → Bool) : valuationOf q 39 = true ∨ valuationOf q 1512 = true := by
  have hs : count1512 q = (countLit q [-39]) + (countLit q [-41]) := List.countP_append (p := literal q) (l₁ := [-39]) (l₂ := [-41])
  have hm := merge_left (literal (valuationOf q) (-39)) (literal (valuationOf q) (1512)) (countLit q [-39]) (countLit q [-41]) (count1512 q) 1 (meaningNeg39 q) (meaning1512 q) hs
  change (! (valuationOf q 39)) = false ∨ valuationOf q 1512 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause948 (q : Snake 81) (h : Conditions q) : valuation q 39 = true ∨ valuation q 1512 = true := counterClause948 (baseVal q)

theorem counterClause949 (q : Nat → Bool) : valuationOf q 39 = true ∨ valuationOf q 41 = true ∨ valuationOf q 1513 = true := by
  have hs : count1512 q = (countLit q [-39]) + (countLit q [-41]) := List.countP_append (p := literal q) (l₁ := [-39]) (l₂ := [-41])
  have hm := merge_two (literal (valuationOf q) (-39)) (literal (valuationOf q) (-41)) (literal (valuationOf q) (1513)) (countLit q [-39]) (countLit q [-41]) (count1512 q) 1 1 (meaningNeg39 q) (meaningNeg41 q) (meaning1513 q) hs
  change (! (valuationOf q 39)) = false ∨ (! (valuationOf q 41)) = false ∨ valuationOf q 1513 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause949 (q : Snake 81) (h : Conditions q) : valuation q 39 = true ∨ valuation q 41 = true ∨ valuation q 1513 = true := counterClause949 (baseVal q)

theorem counterClause950 (q : Nat → Bool) : valuationOf q 1512 = false ∨ valuationOf q 1514 = true := by
  have hs : count1514 q = (countLit q [-36, -37]) + (countLit q [-39, -41]) := List.countP_append (p := literal q) (l₁ := [-36, -37]) (l₂ := [-39, -41])
  have hm := merge_right (literal (valuationOf q) (1512)) (literal (valuationOf q) (1514)) (countLit q [-36, -37]) (countLit q [-39, -41]) (count1514 q) 1 (meaning1512 q) (meaning1514 q) hs
  change valuationOf q 1512 = false ∨ valuationOf q 1514 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause950 (q : Snake 81) (h : Conditions q) : valuation q 1512 = false ∨ valuation q 1514 = true := counterClause950 (baseVal q)

theorem counterClause951 (q : Nat → Bool) : valuationOf q 1513 = false ∨ valuationOf q 1515 = true := by
  have hs : count1514 q = (countLit q [-36, -37]) + (countLit q [-39, -41]) := List.countP_append (p := literal q) (l₁ := [-36, -37]) (l₂ := [-39, -41])
  have hm := merge_right (literal (valuationOf q) (1513)) (literal (valuationOf q) (1515)) (countLit q [-36, -37]) (countLit q [-39, -41]) (count1514 q) 2 (meaning1513 q) (meaning1515 q) hs
  change valuationOf q 1513 = false ∨ valuationOf q 1515 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause951 (q : Snake 81) (h : Conditions q) : valuation q 1513 = false ∨ valuation q 1515 = true := counterClause951 (baseVal q)

theorem counterClause952 (q : Nat → Bool) : valuationOf q 1510 = false ∨ valuationOf q 1514 = true := by
  have hs : count1514 q = (countLit q [-36, -37]) + (countLit q [-39, -41]) := List.countP_append (p := literal q) (l₁ := [-36, -37]) (l₂ := [-39, -41])
  have hm := merge_left (literal (valuationOf q) (1510)) (literal (valuationOf q) (1514)) (countLit q [-36, -37]) (countLit q [-39, -41]) (count1514 q) 1 (meaning1510 q) (meaning1514 q) hs
  change valuationOf q 1510 = false ∨ valuationOf q 1514 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause952 (q : Snake 81) (h : Conditions q) : valuation q 1510 = false ∨ valuation q 1514 = true := counterClause952 (baseVal q)

theorem counterClause953 (q : Nat → Bool) : valuationOf q 1510 = false ∨ valuationOf q 1512 = false ∨ valuationOf q 1515 = true := by
  have hs : count1514 q = (countLit q [-36, -37]) + (countLit q [-39, -41]) := List.countP_append (p := literal q) (l₁ := [-36, -37]) (l₂ := [-39, -41])
  have hm := merge_two (literal (valuationOf q) (1510)) (literal (valuationOf q) (1512)) (literal (valuationOf q) (1515)) (countLit q [-36, -37]) (countLit q [-39, -41]) (count1514 q) 1 1 (meaning1510 q) (meaning1512 q) (meaning1515 q) hs
  change valuationOf q 1510 = false ∨ valuationOf q 1512 = false ∨ valuationOf q 1515 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause953 (q : Snake 81) (h : Conditions q) : valuation q 1510 = false ∨ valuation q 1512 = false ∨ valuation q 1515 = true := counterClause953 (baseVal q)

theorem counterClause954 (q : Nat → Bool) : valuationOf q 1510 = false ∨ valuationOf q 1513 = false ∨ valuationOf q 1516 = true := by
  have hs : count1514 q = (countLit q [-36, -37]) + (countLit q [-39, -41]) := List.countP_append (p := literal q) (l₁ := [-36, -37]) (l₂ := [-39, -41])
  have hm := merge_two (literal (valuationOf q) (1510)) (literal (valuationOf q) (1513)) (literal (valuationOf q) (1516)) (countLit q [-36, -37]) (countLit q [-39, -41]) (count1514 q) 1 2 (meaning1510 q) (meaning1513 q) (meaning1516 q) hs
  change valuationOf q 1510 = false ∨ valuationOf q 1513 = false ∨ valuationOf q 1516 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause954 (q : Snake 81) (h : Conditions q) : valuation q 1510 = false ∨ valuation q 1513 = false ∨ valuation q 1516 = true := counterClause954 (baseVal q)

theorem counterClause955 (q : Nat → Bool) : valuationOf q 1511 = false ∨ valuationOf q 1515 = true := by
  have hs : count1514 q = (countLit q [-36, -37]) + (countLit q [-39, -41]) := List.countP_append (p := literal q) (l₁ := [-36, -37]) (l₂ := [-39, -41])
  have hm := merge_left (literal (valuationOf q) (1511)) (literal (valuationOf q) (1515)) (countLit q [-36, -37]) (countLit q [-39, -41]) (count1514 q) 2 (meaning1511 q) (meaning1515 q) hs
  change valuationOf q 1511 = false ∨ valuationOf q 1515 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause955 (q : Snake 81) (h : Conditions q) : valuation q 1511 = false ∨ valuation q 1515 = true := counterClause955 (baseVal q)

theorem counterClause956 (q : Nat → Bool) : valuationOf q 1511 = false ∨ valuationOf q 1512 = false ∨ valuationOf q 1516 = true := by
  have hs : count1514 q = (countLit q [-36, -37]) + (countLit q [-39, -41]) := List.countP_append (p := literal q) (l₁ := [-36, -37]) (l₂ := [-39, -41])
  have hm := merge_two (literal (valuationOf q) (1511)) (literal (valuationOf q) (1512)) (literal (valuationOf q) (1516)) (countLit q [-36, -37]) (countLit q [-39, -41]) (count1514 q) 2 1 (meaning1511 q) (meaning1512 q) (meaning1516 q) hs
  change valuationOf q 1511 = false ∨ valuationOf q 1512 = false ∨ valuationOf q 1516 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause956 (q : Snake 81) (h : Conditions q) : valuation q 1511 = false ∨ valuation q 1512 = false ∨ valuation q 1516 = true := counterClause956 (baseVal q)

theorem counterClause957 (q : Nat → Bool) : valuationOf q 1511 = false ∨ valuationOf q 1513 = false ∨ valuationOf q 1517 = true := by
  have hs : count1514 q = (countLit q [-36, -37]) + (countLit q [-39, -41]) := List.countP_append (p := literal q) (l₁ := [-36, -37]) (l₂ := [-39, -41])
  have hm := merge_two (literal (valuationOf q) (1511)) (literal (valuationOf q) (1513)) (literal (valuationOf q) (1517)) (countLit q [-36, -37]) (countLit q [-39, -41]) (count1514 q) 2 2 (meaning1511 q) (meaning1513 q) (meaning1517 q) hs
  change valuationOf q 1511 = false ∨ valuationOf q 1513 = false ∨ valuationOf q 1517 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause957 (q : Snake 81) (h : Conditions q) : valuation q 1511 = false ∨ valuation q 1513 = false ∨ valuation q 1517 = true := counterClause957 (baseVal q)

theorem counterClause958 (q : Nat → Bool) : valuationOf q 1514 = false ∨ valuationOf q 1518 = true := by
  have hs : count1518 q = (countLit q [-28, -31, -33, -35]) + (countLit q [-36, -37, -39, -41]) := List.countP_append (p := literal q) (l₁ := [-28, -31, -33, -35]) (l₂ := [-36, -37, -39, -41])
  have hm := merge_right (literal (valuationOf q) (1514)) (literal (valuationOf q) (1518)) (countLit q [-28, -31, -33, -35]) (countLit q [-36, -37, -39, -41]) (count1518 q) 1 (meaning1514 q) (meaning1518 q) hs
  change valuationOf q 1514 = false ∨ valuationOf q 1518 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause958 (q : Snake 81) (h : Conditions q) : valuation q 1514 = false ∨ valuation q 1518 = true := counterClause958 (baseVal q)

theorem counterClause959 (q : Nat → Bool) : valuationOf q 1515 = false ∨ valuationOf q 1519 = true := by
  have hs : count1518 q = (countLit q [-28, -31, -33, -35]) + (countLit q [-36, -37, -39, -41]) := List.countP_append (p := literal q) (l₁ := [-28, -31, -33, -35]) (l₂ := [-36, -37, -39, -41])
  have hm := merge_right (literal (valuationOf q) (1515)) (literal (valuationOf q) (1519)) (countLit q [-28, -31, -33, -35]) (countLit q [-36, -37, -39, -41]) (count1518 q) 2 (meaning1515 q) (meaning1519 q) hs
  change valuationOf q 1515 = false ∨ valuationOf q 1519 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause959 (q : Snake 81) (h : Conditions q) : valuation q 1515 = false ∨ valuation q 1519 = true := counterClause959 (baseVal q)

theorem counterClause960 (q : Nat → Bool) : valuationOf q 1516 = false ∨ valuationOf q 1520 = true := by
  have hs : count1518 q = (countLit q [-28, -31, -33, -35]) + (countLit q [-36, -37, -39, -41]) := List.countP_append (p := literal q) (l₁ := [-28, -31, -33, -35]) (l₂ := [-36, -37, -39, -41])
  have hm := merge_right (literal (valuationOf q) (1516)) (literal (valuationOf q) (1520)) (countLit q [-28, -31, -33, -35]) (countLit q [-36, -37, -39, -41]) (count1518 q) 3 (meaning1516 q) (meaning1520 q) hs
  change valuationOf q 1516 = false ∨ valuationOf q 1520 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause960 (q : Snake 81) (h : Conditions q) : valuation q 1516 = false ∨ valuation q 1520 = true := counterClause960 (baseVal q)

theorem block29 (q : Snake 81) (h : Conditions q) : B112E026.Block29 (valuation q) :=
  ⟨clause929 q h, clause930 q h, clause931 q h, clause932 q h, clause933 q h, clause934 q h, clause935 q h, clause936 q h, clause937 q h, clause938 q h, clause939 q h, clause940 q h, clause941 q h, clause942 q h, clause943 q h, clause944 q h, clause945 q h, clause946 q h, clause947 q h, clause948 q h, clause949 q h, clause950 q h, clause951 q h, clause952 q h, clause953 q h, clause954 q h, clause955 q h, clause956 q h, clause957 q h, clause958 q h, clause959 q h, clause960 q h⟩

end
end Snake9.Regrowth.E112026
