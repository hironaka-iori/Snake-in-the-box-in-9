import E112007Semantics
import B112E007Inputs
namespace Snake9.Regrowth.E112007
noncomputable section
local instance blockDec29 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause929 (q : Nat → Bool) : valuationOf q 34 = true ∨ valuationOf q 1501 = true := by
  have hs : count1501 q = (countLit q [-34]) + (countLit q [-36, -37]) := List.countP_append (p := literal q) (l₁ := [-34]) (l₂ := [-36, -37])
  have hm := merge_left (literal (valuationOf q) (-34)) (literal (valuationOf q) (1501)) (countLit q [-34]) (countLit q [-36, -37]) (count1501 q) 1 (meaningNeg34 q) (meaning1501 q) hs
  change (! (valuationOf q 34)) = false ∨ valuationOf q 1501 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause929 (q : Snake 81) (h : Conditions q) : valuation q 34 = true ∨ valuation q 1501 = true := counterClause929 (baseVal q)

theorem counterClause930 (q : Nat → Bool) : valuationOf q 34 = true ∨ valuationOf q 1499 = false ∨ valuationOf q 1502 = true := by
  have hs : count1501 q = (countLit q [-34]) + (countLit q [-36, -37]) := List.countP_append (p := literal q) (l₁ := [-34]) (l₂ := [-36, -37])
  have hm := merge_two (literal (valuationOf q) (-34)) (literal (valuationOf q) (1499)) (literal (valuationOf q) (1502)) (countLit q [-34]) (countLit q [-36, -37]) (count1501 q) 1 1 (meaningNeg34 q) (meaning1499 q) (meaning1502 q) hs
  change (! (valuationOf q 34)) = false ∨ valuationOf q 1499 = false ∨ valuationOf q 1502 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause930 (q : Snake 81) (h : Conditions q) : valuation q 34 = true ∨ valuation q 1499 = false ∨ valuation q 1502 = true := counterClause930 (baseVal q)

theorem counterClause931 (q : Nat → Bool) : valuationOf q 42 = true ∨ valuationOf q 1504 = true := by
  have hs : count1504 q = (countLit q [-40]) + (countLit q [-42]) := List.countP_append (p := literal q) (l₁ := [-40]) (l₂ := [-42])
  have hm := merge_right (literal (valuationOf q) (-42)) (literal (valuationOf q) (1504)) (countLit q [-40]) (countLit q [-42]) (count1504 q) 1 (meaningNeg42 q) (meaning1504 q) hs
  change (! (valuationOf q 42)) = false ∨ valuationOf q 1504 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause931 (q : Snake 81) (h : Conditions q) : valuation q 42 = true ∨ valuation q 1504 = true := counterClause931 (baseVal q)

theorem counterClause932 (q : Nat → Bool) : valuationOf q 40 = true ∨ valuationOf q 1504 = true := by
  have hs : count1504 q = (countLit q [-40]) + (countLit q [-42]) := List.countP_append (p := literal q) (l₁ := [-40]) (l₂ := [-42])
  have hm := merge_left (literal (valuationOf q) (-40)) (literal (valuationOf q) (1504)) (countLit q [-40]) (countLit q [-42]) (count1504 q) 1 (meaningNeg40 q) (meaning1504 q) hs
  change (! (valuationOf q 40)) = false ∨ valuationOf q 1504 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause932 (q : Snake 81) (h : Conditions q) : valuation q 40 = true ∨ valuation q 1504 = true := counterClause932 (baseVal q)

theorem counterClause933 (q : Nat → Bool) : valuationOf q 40 = true ∨ valuationOf q 42 = true ∨ valuationOf q 1505 = true := by
  have hs : count1504 q = (countLit q [-40]) + (countLit q [-42]) := List.countP_append (p := literal q) (l₁ := [-40]) (l₂ := [-42])
  have hm := merge_two (literal (valuationOf q) (-40)) (literal (valuationOf q) (-42)) (literal (valuationOf q) (1505)) (countLit q [-40]) (countLit q [-42]) (count1504 q) 1 1 (meaningNeg40 q) (meaningNeg42 q) (meaning1505 q) hs
  change (! (valuationOf q 40)) = false ∨ (! (valuationOf q 42)) = false ∨ valuationOf q 1505 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause933 (q : Snake 81) (h : Conditions q) : valuation q 40 = true ∨ valuation q 42 = true ∨ valuation q 1505 = true := counterClause933 (baseVal q)

theorem counterClause934 (q : Nat → Bool) : valuationOf q 46 = true ∨ valuationOf q 1506 = true := by
  have hs : count1506 q = (countLit q [-43]) + (countLit q [-46]) := List.countP_append (p := literal q) (l₁ := [-43]) (l₂ := [-46])
  have hm := merge_right (literal (valuationOf q) (-46)) (literal (valuationOf q) (1506)) (countLit q [-43]) (countLit q [-46]) (count1506 q) 1 (meaningNeg46 q) (meaning1506 q) hs
  change (! (valuationOf q 46)) = false ∨ valuationOf q 1506 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause934 (q : Snake 81) (h : Conditions q) : valuation q 46 = true ∨ valuation q 1506 = true := counterClause934 (baseVal q)

theorem counterClause935 (q : Nat → Bool) : valuationOf q 43 = true ∨ valuationOf q 1506 = true := by
  have hs : count1506 q = (countLit q [-43]) + (countLit q [-46]) := List.countP_append (p := literal q) (l₁ := [-43]) (l₂ := [-46])
  have hm := merge_left (literal (valuationOf q) (-43)) (literal (valuationOf q) (1506)) (countLit q [-43]) (countLit q [-46]) (count1506 q) 1 (meaningNeg43 q) (meaning1506 q) hs
  change (! (valuationOf q 43)) = false ∨ valuationOf q 1506 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause935 (q : Snake 81) (h : Conditions q) : valuation q 43 = true ∨ valuation q 1506 = true := counterClause935 (baseVal q)

theorem counterClause936 (q : Nat → Bool) : valuationOf q 43 = true ∨ valuationOf q 46 = true ∨ valuationOf q 1507 = true := by
  have hs : count1506 q = (countLit q [-43]) + (countLit q [-46]) := List.countP_append (p := literal q) (l₁ := [-43]) (l₂ := [-46])
  have hm := merge_two (literal (valuationOf q) (-43)) (literal (valuationOf q) (-46)) (literal (valuationOf q) (1507)) (countLit q [-43]) (countLit q [-46]) (count1506 q) 1 1 (meaningNeg43 q) (meaningNeg46 q) (meaning1507 q) hs
  change (! (valuationOf q 43)) = false ∨ (! (valuationOf q 46)) = false ∨ valuationOf q 1507 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause936 (q : Snake 81) (h : Conditions q) : valuation q 43 = true ∨ valuation q 46 = true ∨ valuation q 1507 = true := counterClause936 (baseVal q)

theorem counterClause937 (q : Nat → Bool) : valuationOf q 1506 = false ∨ valuationOf q 1508 = true := by
  have hs : count1508 q = (countLit q [-40, -42]) + (countLit q [-43, -46]) := List.countP_append (p := literal q) (l₁ := [-40, -42]) (l₂ := [-43, -46])
  have hm := merge_right (literal (valuationOf q) (1506)) (literal (valuationOf q) (1508)) (countLit q [-40, -42]) (countLit q [-43, -46]) (count1508 q) 1 (meaning1506 q) (meaning1508 q) hs
  change valuationOf q 1506 = false ∨ valuationOf q 1508 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause937 (q : Snake 81) (h : Conditions q) : valuation q 1506 = false ∨ valuation q 1508 = true := counterClause937 (baseVal q)

theorem counterClause938 (q : Nat → Bool) : valuationOf q 1507 = false ∨ valuationOf q 1509 = true := by
  have hs : count1508 q = (countLit q [-40, -42]) + (countLit q [-43, -46]) := List.countP_append (p := literal q) (l₁ := [-40, -42]) (l₂ := [-43, -46])
  have hm := merge_right (literal (valuationOf q) (1507)) (literal (valuationOf q) (1509)) (countLit q [-40, -42]) (countLit q [-43, -46]) (count1508 q) 2 (meaning1507 q) (meaning1509 q) hs
  change valuationOf q 1507 = false ∨ valuationOf q 1509 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause938 (q : Snake 81) (h : Conditions q) : valuation q 1507 = false ∨ valuation q 1509 = true := counterClause938 (baseVal q)

theorem counterClause939 (q : Nat → Bool) : valuationOf q 1504 = false ∨ valuationOf q 1508 = true := by
  have hs : count1508 q = (countLit q [-40, -42]) + (countLit q [-43, -46]) := List.countP_append (p := literal q) (l₁ := [-40, -42]) (l₂ := [-43, -46])
  have hm := merge_left (literal (valuationOf q) (1504)) (literal (valuationOf q) (1508)) (countLit q [-40, -42]) (countLit q [-43, -46]) (count1508 q) 1 (meaning1504 q) (meaning1508 q) hs
  change valuationOf q 1504 = false ∨ valuationOf q 1508 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause939 (q : Snake 81) (h : Conditions q) : valuation q 1504 = false ∨ valuation q 1508 = true := counterClause939 (baseVal q)

theorem counterClause940 (q : Nat → Bool) : valuationOf q 1504 = false ∨ valuationOf q 1506 = false ∨ valuationOf q 1509 = true := by
  have hs : count1508 q = (countLit q [-40, -42]) + (countLit q [-43, -46]) := List.countP_append (p := literal q) (l₁ := [-40, -42]) (l₂ := [-43, -46])
  have hm := merge_two (literal (valuationOf q) (1504)) (literal (valuationOf q) (1506)) (literal (valuationOf q) (1509)) (countLit q [-40, -42]) (countLit q [-43, -46]) (count1508 q) 1 1 (meaning1504 q) (meaning1506 q) (meaning1509 q) hs
  change valuationOf q 1504 = false ∨ valuationOf q 1506 = false ∨ valuationOf q 1509 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause940 (q : Snake 81) (h : Conditions q) : valuation q 1504 = false ∨ valuation q 1506 = false ∨ valuation q 1509 = true := counterClause940 (baseVal q)

theorem counterClause941 (q : Nat → Bool) : valuationOf q 1504 = false ∨ valuationOf q 1507 = false ∨ valuationOf q 1510 = true := by
  have hs : count1508 q = (countLit q [-40, -42]) + (countLit q [-43, -46]) := List.countP_append (p := literal q) (l₁ := [-40, -42]) (l₂ := [-43, -46])
  have hm := merge_two (literal (valuationOf q) (1504)) (literal (valuationOf q) (1507)) (literal (valuationOf q) (1510)) (countLit q [-40, -42]) (countLit q [-43, -46]) (count1508 q) 1 2 (meaning1504 q) (meaning1507 q) (meaning1510 q) hs
  change valuationOf q 1504 = false ∨ valuationOf q 1507 = false ∨ valuationOf q 1510 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause941 (q : Snake 81) (h : Conditions q) : valuation q 1504 = false ∨ valuation q 1507 = false ∨ valuation q 1510 = true := counterClause941 (baseVal q)

theorem counterClause942 (q : Nat → Bool) : valuationOf q 1505 = false ∨ valuationOf q 1509 = true := by
  have hs : count1508 q = (countLit q [-40, -42]) + (countLit q [-43, -46]) := List.countP_append (p := literal q) (l₁ := [-40, -42]) (l₂ := [-43, -46])
  have hm := merge_left (literal (valuationOf q) (1505)) (literal (valuationOf q) (1509)) (countLit q [-40, -42]) (countLit q [-43, -46]) (count1508 q) 2 (meaning1505 q) (meaning1509 q) hs
  change valuationOf q 1505 = false ∨ valuationOf q 1509 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause942 (q : Snake 81) (h : Conditions q) : valuation q 1505 = false ∨ valuation q 1509 = true := counterClause942 (baseVal q)

theorem counterClause943 (q : Nat → Bool) : valuationOf q 1505 = false ∨ valuationOf q 1506 = false ∨ valuationOf q 1510 = true := by
  have hs : count1508 q = (countLit q [-40, -42]) + (countLit q [-43, -46]) := List.countP_append (p := literal q) (l₁ := [-40, -42]) (l₂ := [-43, -46])
  have hm := merge_two (literal (valuationOf q) (1505)) (literal (valuationOf q) (1506)) (literal (valuationOf q) (1510)) (countLit q [-40, -42]) (countLit q [-43, -46]) (count1508 q) 2 1 (meaning1505 q) (meaning1506 q) (meaning1510 q) hs
  change valuationOf q 1505 = false ∨ valuationOf q 1506 = false ∨ valuationOf q 1510 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause943 (q : Snake 81) (h : Conditions q) : valuation q 1505 = false ∨ valuation q 1506 = false ∨ valuation q 1510 = true := counterClause943 (baseVal q)

theorem counterClause944 (q : Nat → Bool) : valuationOf q 1505 = false ∨ valuationOf q 1507 = false ∨ valuationOf q 1511 = true := by
  have hs : count1508 q = (countLit q [-40, -42]) + (countLit q [-43, -46]) := List.countP_append (p := literal q) (l₁ := [-40, -42]) (l₂ := [-43, -46])
  have hm := merge_two (literal (valuationOf q) (1505)) (literal (valuationOf q) (1507)) (literal (valuationOf q) (1511)) (countLit q [-40, -42]) (countLit q [-43, -46]) (count1508 q) 2 2 (meaning1505 q) (meaning1507 q) (meaning1511 q) hs
  change valuationOf q 1505 = false ∨ valuationOf q 1507 = false ∨ valuationOf q 1511 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause944 (q : Snake 81) (h : Conditions q) : valuation q 1505 = false ∨ valuation q 1507 = false ∨ valuation q 1511 = true := counterClause944 (baseVal q)

theorem counterClause945 (q : Nat → Bool) : valuationOf q 1508 = false ∨ valuationOf q 1512 = true := by
  have hs : count1512 q = (countLit q [-34, -36, -37]) + (countLit q [-40, -42, -43, -46]) := List.countP_append (p := literal q) (l₁ := [-34, -36, -37]) (l₂ := [-40, -42, -43, -46])
  have hm := merge_right (literal (valuationOf q) (1508)) (literal (valuationOf q) (1512)) (countLit q [-34, -36, -37]) (countLit q [-40, -42, -43, -46]) (count1512 q) 1 (meaning1508 q) (meaning1512 q) hs
  change valuationOf q 1508 = false ∨ valuationOf q 1512 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause945 (q : Snake 81) (h : Conditions q) : valuation q 1508 = false ∨ valuation q 1512 = true := counterClause945 (baseVal q)

theorem counterClause946 (q : Nat → Bool) : valuationOf q 1509 = false ∨ valuationOf q 1513 = true := by
  have hs : count1512 q = (countLit q [-34, -36, -37]) + (countLit q [-40, -42, -43, -46]) := List.countP_append (p := literal q) (l₁ := [-34, -36, -37]) (l₂ := [-40, -42, -43, -46])
  have hm := merge_right (literal (valuationOf q) (1509)) (literal (valuationOf q) (1513)) (countLit q [-34, -36, -37]) (countLit q [-40, -42, -43, -46]) (count1512 q) 2 (meaning1509 q) (meaning1513 q) hs
  change valuationOf q 1509 = false ∨ valuationOf q 1513 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause946 (q : Snake 81) (h : Conditions q) : valuation q 1509 = false ∨ valuation q 1513 = true := counterClause946 (baseVal q)

theorem counterClause947 (q : Nat → Bool) : valuationOf q 1510 = false ∨ valuationOf q 1514 = true := by
  have hs : count1512 q = (countLit q [-34, -36, -37]) + (countLit q [-40, -42, -43, -46]) := List.countP_append (p := literal q) (l₁ := [-34, -36, -37]) (l₂ := [-40, -42, -43, -46])
  have hm := merge_right (literal (valuationOf q) (1510)) (literal (valuationOf q) (1514)) (countLit q [-34, -36, -37]) (countLit q [-40, -42, -43, -46]) (count1512 q) 3 (meaning1510 q) (meaning1514 q) hs
  change valuationOf q 1510 = false ∨ valuationOf q 1514 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause947 (q : Snake 81) (h : Conditions q) : valuation q 1510 = false ∨ valuation q 1514 = true := counterClause947 (baseVal q)

theorem counterClause948 (q : Nat → Bool) : valuationOf q 1511 = false ∨ valuationOf q 1515 = true := by
  have hs : count1512 q = (countLit q [-34, -36, -37]) + (countLit q [-40, -42, -43, -46]) := List.countP_append (p := literal q) (l₁ := [-34, -36, -37]) (l₂ := [-40, -42, -43, -46])
  have hm := merge_right (literal (valuationOf q) (1511)) (literal (valuationOf q) (1515)) (countLit q [-34, -36, -37]) (countLit q [-40, -42, -43, -46]) (count1512 q) 4 (meaning1511 q) (meaning1515 q) hs
  change valuationOf q 1511 = false ∨ valuationOf q 1515 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause948 (q : Snake 81) (h : Conditions q) : valuation q 1511 = false ∨ valuation q 1515 = true := counterClause948 (baseVal q)

theorem counterClause949 (q : Nat → Bool) : valuationOf q 1501 = false ∨ valuationOf q 1512 = true := by
  have hs : count1512 q = (countLit q [-34, -36, -37]) + (countLit q [-40, -42, -43, -46]) := List.countP_append (p := literal q) (l₁ := [-34, -36, -37]) (l₂ := [-40, -42, -43, -46])
  have hm := merge_left (literal (valuationOf q) (1501)) (literal (valuationOf q) (1512)) (countLit q [-34, -36, -37]) (countLit q [-40, -42, -43, -46]) (count1512 q) 1 (meaning1501 q) (meaning1512 q) hs
  change valuationOf q 1501 = false ∨ valuationOf q 1512 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause949 (q : Snake 81) (h : Conditions q) : valuation q 1501 = false ∨ valuation q 1512 = true := counterClause949 (baseVal q)

theorem counterClause950 (q : Nat → Bool) : valuationOf q 1501 = false ∨ valuationOf q 1508 = false ∨ valuationOf q 1513 = true := by
  have hs : count1512 q = (countLit q [-34, -36, -37]) + (countLit q [-40, -42, -43, -46]) := List.countP_append (p := literal q) (l₁ := [-34, -36, -37]) (l₂ := [-40, -42, -43, -46])
  have hm := merge_two (literal (valuationOf q) (1501)) (literal (valuationOf q) (1508)) (literal (valuationOf q) (1513)) (countLit q [-34, -36, -37]) (countLit q [-40, -42, -43, -46]) (count1512 q) 1 1 (meaning1501 q) (meaning1508 q) (meaning1513 q) hs
  change valuationOf q 1501 = false ∨ valuationOf q 1508 = false ∨ valuationOf q 1513 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause950 (q : Snake 81) (h : Conditions q) : valuation q 1501 = false ∨ valuation q 1508 = false ∨ valuation q 1513 = true := counterClause950 (baseVal q)

theorem counterClause951 (q : Nat → Bool) : valuationOf q 1501 = false ∨ valuationOf q 1509 = false ∨ valuationOf q 1514 = true := by
  have hs : count1512 q = (countLit q [-34, -36, -37]) + (countLit q [-40, -42, -43, -46]) := List.countP_append (p := literal q) (l₁ := [-34, -36, -37]) (l₂ := [-40, -42, -43, -46])
  have hm := merge_two (literal (valuationOf q) (1501)) (literal (valuationOf q) (1509)) (literal (valuationOf q) (1514)) (countLit q [-34, -36, -37]) (countLit q [-40, -42, -43, -46]) (count1512 q) 1 2 (meaning1501 q) (meaning1509 q) (meaning1514 q) hs
  change valuationOf q 1501 = false ∨ valuationOf q 1509 = false ∨ valuationOf q 1514 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause951 (q : Snake 81) (h : Conditions q) : valuation q 1501 = false ∨ valuation q 1509 = false ∨ valuation q 1514 = true := counterClause951 (baseVal q)

theorem counterClause952 (q : Nat → Bool) : valuationOf q 1501 = false ∨ valuationOf q 1510 = false ∨ valuationOf q 1515 = true := by
  have hs : count1512 q = (countLit q [-34, -36, -37]) + (countLit q [-40, -42, -43, -46]) := List.countP_append (p := literal q) (l₁ := [-34, -36, -37]) (l₂ := [-40, -42, -43, -46])
  have hm := merge_two (literal (valuationOf q) (1501)) (literal (valuationOf q) (1510)) (literal (valuationOf q) (1515)) (countLit q [-34, -36, -37]) (countLit q [-40, -42, -43, -46]) (count1512 q) 1 3 (meaning1501 q) (meaning1510 q) (meaning1515 q) hs
  change valuationOf q 1501 = false ∨ valuationOf q 1510 = false ∨ valuationOf q 1515 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause952 (q : Snake 81) (h : Conditions q) : valuation q 1501 = false ∨ valuation q 1510 = false ∨ valuation q 1515 = true := counterClause952 (baseVal q)

theorem counterClause953 (q : Nat → Bool) : valuationOf q 1501 = false ∨ valuationOf q 1511 = false ∨ valuationOf q 1516 = true := by
  have hs : count1512 q = (countLit q [-34, -36, -37]) + (countLit q [-40, -42, -43, -46]) := List.countP_append (p := literal q) (l₁ := [-34, -36, -37]) (l₂ := [-40, -42, -43, -46])
  have hm := merge_two (literal (valuationOf q) (1501)) (literal (valuationOf q) (1511)) (literal (valuationOf q) (1516)) (countLit q [-34, -36, -37]) (countLit q [-40, -42, -43, -46]) (count1512 q) 1 4 (meaning1501 q) (meaning1511 q) (meaning1516 q) hs
  change valuationOf q 1501 = false ∨ valuationOf q 1511 = false ∨ valuationOf q 1516 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause953 (q : Snake 81) (h : Conditions q) : valuation q 1501 = false ∨ valuation q 1511 = false ∨ valuation q 1516 = true := counterClause953 (baseVal q)

theorem counterClause954 (q : Nat → Bool) : valuationOf q 1502 = false ∨ valuationOf q 1513 = true := by
  have hs : count1512 q = (countLit q [-34, -36, -37]) + (countLit q [-40, -42, -43, -46]) := List.countP_append (p := literal q) (l₁ := [-34, -36, -37]) (l₂ := [-40, -42, -43, -46])
  have hm := merge_left (literal (valuationOf q) (1502)) (literal (valuationOf q) (1513)) (countLit q [-34, -36, -37]) (countLit q [-40, -42, -43, -46]) (count1512 q) 2 (meaning1502 q) (meaning1513 q) hs
  change valuationOf q 1502 = false ∨ valuationOf q 1513 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause954 (q : Snake 81) (h : Conditions q) : valuation q 1502 = false ∨ valuation q 1513 = true := counterClause954 (baseVal q)

theorem counterClause955 (q : Nat → Bool) : valuationOf q 1502 = false ∨ valuationOf q 1508 = false ∨ valuationOf q 1514 = true := by
  have hs : count1512 q = (countLit q [-34, -36, -37]) + (countLit q [-40, -42, -43, -46]) := List.countP_append (p := literal q) (l₁ := [-34, -36, -37]) (l₂ := [-40, -42, -43, -46])
  have hm := merge_two (literal (valuationOf q) (1502)) (literal (valuationOf q) (1508)) (literal (valuationOf q) (1514)) (countLit q [-34, -36, -37]) (countLit q [-40, -42, -43, -46]) (count1512 q) 2 1 (meaning1502 q) (meaning1508 q) (meaning1514 q) hs
  change valuationOf q 1502 = false ∨ valuationOf q 1508 = false ∨ valuationOf q 1514 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause955 (q : Snake 81) (h : Conditions q) : valuation q 1502 = false ∨ valuation q 1508 = false ∨ valuation q 1514 = true := counterClause955 (baseVal q)

theorem counterClause956 (q : Nat → Bool) : valuationOf q 1502 = false ∨ valuationOf q 1511 = false ∨ valuationOf q 1517 = true := by
  have hs : count1512 q = (countLit q [-34, -36, -37]) + (countLit q [-40, -42, -43, -46]) := List.countP_append (p := literal q) (l₁ := [-34, -36, -37]) (l₂ := [-40, -42, -43, -46])
  have hm := merge_two (literal (valuationOf q) (1502)) (literal (valuationOf q) (1511)) (literal (valuationOf q) (1517)) (countLit q [-34, -36, -37]) (countLit q [-40, -42, -43, -46]) (count1512 q) 2 4 (meaning1502 q) (meaning1511 q) (meaning1517 q) hs
  change valuationOf q 1502 = false ∨ valuationOf q 1511 = false ∨ valuationOf q 1517 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause956 (q : Snake 81) (h : Conditions q) : valuation q 1502 = false ∨ valuation q 1511 = false ∨ valuation q 1517 = true := counterClause956 (baseVal q)

theorem counterClause957 (q : Nat → Bool) : valuationOf q 52 = true ∨ valuationOf q 1519 = true := by
  have hs : count1519 q = (countLit q [-51]) + (countLit q [-52]) := List.countP_append (p := literal q) (l₁ := [-51]) (l₂ := [-52])
  have hm := merge_right (literal (valuationOf q) (-52)) (literal (valuationOf q) (1519)) (countLit q [-51]) (countLit q [-52]) (count1519 q) 1 (meaningNeg52 q) (meaning1519 q) hs
  change (! (valuationOf q 52)) = false ∨ valuationOf q 1519 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause957 (q : Snake 81) (h : Conditions q) : valuation q 52 = true ∨ valuation q 1519 = true := counterClause957 (baseVal q)

theorem counterClause958 (q : Nat → Bool) : valuationOf q 51 = true ∨ valuationOf q 1519 = true := by
  have hs : count1519 q = (countLit q [-51]) + (countLit q [-52]) := List.countP_append (p := literal q) (l₁ := [-51]) (l₂ := [-52])
  have hm := merge_left (literal (valuationOf q) (-51)) (literal (valuationOf q) (1519)) (countLit q [-51]) (countLit q [-52]) (count1519 q) 1 (meaningNeg51 q) (meaning1519 q) hs
  change (! (valuationOf q 51)) = false ∨ valuationOf q 1519 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause958 (q : Snake 81) (h : Conditions q) : valuation q 51 = true ∨ valuation q 1519 = true := counterClause958 (baseVal q)

theorem counterClause959 (q : Nat → Bool) : valuationOf q 51 = true ∨ valuationOf q 52 = true ∨ valuationOf q 1520 = true := by
  have hs : count1519 q = (countLit q [-51]) + (countLit q [-52]) := List.countP_append (p := literal q) (l₁ := [-51]) (l₂ := [-52])
  have hm := merge_two (literal (valuationOf q) (-51)) (literal (valuationOf q) (-52)) (literal (valuationOf q) (1520)) (countLit q [-51]) (countLit q [-52]) (count1519 q) 1 1 (meaningNeg51 q) (meaningNeg52 q) (meaning1520 q) hs
  change (! (valuationOf q 51)) = false ∨ (! (valuationOf q 52)) = false ∨ valuationOf q 1520 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause959 (q : Snake 81) (h : Conditions q) : valuation q 51 = true ∨ valuation q 52 = true ∨ valuation q 1520 = true := counterClause959 (baseVal q)

theorem counterClause960 (q : Nat → Bool) : valuationOf q 1519 = false ∨ valuationOf q 1521 = true := by
  have hs : count1521 q = (countLit q [-47]) + (countLit q [-51, -52]) := List.countP_append (p := literal q) (l₁ := [-47]) (l₂ := [-51, -52])
  have hm := merge_right (literal (valuationOf q) (1519)) (literal (valuationOf q) (1521)) (countLit q [-47]) (countLit q [-51, -52]) (count1521 q) 1 (meaning1519 q) (meaning1521 q) hs
  change valuationOf q 1519 = false ∨ valuationOf q 1521 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause960 (q : Snake 81) (h : Conditions q) : valuation q 1519 = false ∨ valuation q 1521 = true := counterClause960 (baseVal q)

theorem block29 (q : Snake 81) (h : Conditions q) : B112E007.Block29 (valuation q) :=
  ⟨clause929 q h, clause930 q h, clause931 q h, clause932 q h, clause933 q h, clause934 q h, clause935 q h, clause936 q h, clause937 q h, clause938 q h, clause939 q h, clause940 q h, clause941 q h, clause942 q h, clause943 q h, clause944 q h, clause945 q h, clause946 q h, clause947 q h, clause948 q h, clause949 q h, clause950 q h, clause951 q h, clause952 q h, clause953 q h, clause954 q h, clause955 q h, clause956 q h, clause957 q h, clause958 q h, clause959 q h, clause960 q h⟩

end
end Snake9.Regrowth.E112007
