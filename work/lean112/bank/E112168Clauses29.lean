import E112168Semantics
import B112E168Inputs
namespace Snake9.Regrowth.E112168
noncomputable section
local instance blockDec29 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause929 (q : Nat → Bool) : valuationOf q 62 = true ∨ valuationOf q 1497 = true := by
  have hs : count1497 q = (countLit q [-61]) + (countLit q [-62]) := List.countP_append (p := literal q) (l₁ := [-61]) (l₂ := [-62])
  have hm := merge_right (literal (valuationOf q) (-62)) (literal (valuationOf q) (1497)) (countLit q [-61]) (countLit q [-62]) (count1497 q) 1 (meaningNeg62 q) (meaning1497 q) hs
  change (! (valuationOf q 62)) = false ∨ valuationOf q 1497 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause929 (q : Snake 81) (h : Conditions q) : valuation q 62 = true ∨ valuation q 1497 = true := counterClause929 (baseVal q)

theorem counterClause930 (q : Nat → Bool) : valuationOf q 61 = true ∨ valuationOf q 1497 = true := by
  have hs : count1497 q = (countLit q [-61]) + (countLit q [-62]) := List.countP_append (p := literal q) (l₁ := [-61]) (l₂ := [-62])
  have hm := merge_left (literal (valuationOf q) (-61)) (literal (valuationOf q) (1497)) (countLit q [-61]) (countLit q [-62]) (count1497 q) 1 (meaningNeg61 q) (meaning1497 q) hs
  change (! (valuationOf q 61)) = false ∨ valuationOf q 1497 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause930 (q : Snake 81) (h : Conditions q) : valuation q 61 = true ∨ valuation q 1497 = true := counterClause930 (baseVal q)

theorem counterClause931 (q : Nat → Bool) : valuationOf q 61 = true ∨ valuationOf q 62 = true ∨ valuationOf q 1498 = true := by
  have hs : count1497 q = (countLit q [-61]) + (countLit q [-62]) := List.countP_append (p := literal q) (l₁ := [-61]) (l₂ := [-62])
  have hm := merge_two (literal (valuationOf q) (-61)) (literal (valuationOf q) (-62)) (literal (valuationOf q) (1498)) (countLit q [-61]) (countLit q [-62]) (count1497 q) 1 1 (meaningNeg61 q) (meaningNeg62 q) (meaning1498 q) hs
  change (! (valuationOf q 61)) = false ∨ (! (valuationOf q 62)) = false ∨ valuationOf q 1498 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause931 (q : Snake 81) (h : Conditions q) : valuation q 61 = true ∨ valuation q 62 = true ∨ valuation q 1498 = true := counterClause931 (baseVal q)

theorem counterClause932 (q : Nat → Bool) : valuationOf q 1497 = false ∨ valuationOf q 1499 = true := by
  have hs : count1499 q = (countLit q [-60]) + (countLit q [-61, -62]) := List.countP_append (p := literal q) (l₁ := [-60]) (l₂ := [-61, -62])
  have hm := merge_right (literal (valuationOf q) (1497)) (literal (valuationOf q) (1499)) (countLit q [-60]) (countLit q [-61, -62]) (count1499 q) 1 (meaning1497 q) (meaning1499 q) hs
  change valuationOf q 1497 = false ∨ valuationOf q 1499 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause932 (q : Snake 81) (h : Conditions q) : valuation q 1497 = false ∨ valuation q 1499 = true := counterClause932 (baseVal q)

theorem counterClause933 (q : Nat → Bool) : valuationOf q 1498 = false ∨ valuationOf q 1500 = true := by
  have hs : count1499 q = (countLit q [-60]) + (countLit q [-61, -62]) := List.countP_append (p := literal q) (l₁ := [-60]) (l₂ := [-61, -62])
  have hm := merge_right (literal (valuationOf q) (1498)) (literal (valuationOf q) (1500)) (countLit q [-60]) (countLit q [-61, -62]) (count1499 q) 2 (meaning1498 q) (meaning1500 q) hs
  change valuationOf q 1498 = false ∨ valuationOf q 1500 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause933 (q : Snake 81) (h : Conditions q) : valuation q 1498 = false ∨ valuation q 1500 = true := counterClause933 (baseVal q)

theorem counterClause934 (q : Nat → Bool) : valuationOf q 60 = true ∨ valuationOf q 1499 = true := by
  have hs : count1499 q = (countLit q [-60]) + (countLit q [-61, -62]) := List.countP_append (p := literal q) (l₁ := [-60]) (l₂ := [-61, -62])
  have hm := merge_left (literal (valuationOf q) (-60)) (literal (valuationOf q) (1499)) (countLit q [-60]) (countLit q [-61, -62]) (count1499 q) 1 (meaningNeg60 q) (meaning1499 q) hs
  change (! (valuationOf q 60)) = false ∨ valuationOf q 1499 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause934 (q : Snake 81) (h : Conditions q) : valuation q 60 = true ∨ valuation q 1499 = true := counterClause934 (baseVal q)

theorem counterClause935 (q : Nat → Bool) : valuationOf q 60 = true ∨ valuationOf q 1497 = false ∨ valuationOf q 1500 = true := by
  have hs : count1499 q = (countLit q [-60]) + (countLit q [-61, -62]) := List.countP_append (p := literal q) (l₁ := [-60]) (l₂ := [-61, -62])
  have hm := merge_two (literal (valuationOf q) (-60)) (literal (valuationOf q) (1497)) (literal (valuationOf q) (1500)) (countLit q [-60]) (countLit q [-61, -62]) (count1499 q) 1 1 (meaningNeg60 q) (meaning1497 q) (meaning1500 q) hs
  change (! (valuationOf q 60)) = false ∨ valuationOf q 1497 = false ∨ valuationOf q 1500 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause935 (q : Snake 81) (h : Conditions q) : valuation q 60 = true ∨ valuation q 1497 = false ∨ valuation q 1500 = true := counterClause935 (baseVal q)

theorem counterClause936 (q : Nat → Bool) : valuationOf q 60 = true ∨ valuationOf q 1498 = false ∨ valuationOf q 1501 = true := by
  have hs : count1499 q = (countLit q [-60]) + (countLit q [-61, -62]) := List.countP_append (p := literal q) (l₁ := [-60]) (l₂ := [-61, -62])
  have hm := merge_two (literal (valuationOf q) (-60)) (literal (valuationOf q) (1498)) (literal (valuationOf q) (1501)) (countLit q [-60]) (countLit q [-61, -62]) (count1499 q) 1 2 (meaningNeg60 q) (meaning1498 q) (meaning1501 q) hs
  change (! (valuationOf q 60)) = false ∨ valuationOf q 1498 = false ∨ valuationOf q 1501 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause936 (q : Snake 81) (h : Conditions q) : valuation q 60 = true ∨ valuation q 1498 = false ∨ valuation q 1501 = true := counterClause936 (baseVal q)

theorem counterClause937 (q : Nat → Bool) : valuationOf q 66 = true ∨ valuationOf q 1502 = true := by
  have hs : count1502 q = (countLit q [-66]) + (countLit q [-68]) := List.countP_append (p := literal q) (l₁ := [-66]) (l₂ := [-68])
  have hm := merge_left (literal (valuationOf q) (-66)) (literal (valuationOf q) (1502)) (countLit q [-66]) (countLit q [-68]) (count1502 q) 1 (meaningNeg66 q) (meaning1502 q) hs
  change (! (valuationOf q 66)) = false ∨ valuationOf q 1502 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause937 (q : Snake 81) (h : Conditions q) : valuation q 66 = true ∨ valuation q 1502 = true := counterClause937 (baseVal q)

theorem counterClause938 (q : Nat → Bool) : valuationOf q 66 = true ∨ valuationOf q 68 = true ∨ valuationOf q 1503 = true := by
  have hs : count1502 q = (countLit q [-66]) + (countLit q [-68]) := List.countP_append (p := literal q) (l₁ := [-66]) (l₂ := [-68])
  have hm := merge_two (literal (valuationOf q) (-66)) (literal (valuationOf q) (-68)) (literal (valuationOf q) (1503)) (countLit q [-66]) (countLit q [-68]) (count1502 q) 1 1 (meaningNeg66 q) (meaningNeg68 q) (meaning1503 q) hs
  change (! (valuationOf q 66)) = false ∨ (! (valuationOf q 68)) = false ∨ valuationOf q 1503 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause938 (q : Snake 81) (h : Conditions q) : valuation q 66 = true ∨ valuation q 68 = true ∨ valuation q 1503 = true := counterClause938 (baseVal q)

theorem counterClause939 (q : Nat → Bool) : valuationOf q 70 = true ∨ valuationOf q 1504 = true := by
  have hs : count1504 q = (countLit q [-69]) + (countLit q [-70]) := List.countP_append (p := literal q) (l₁ := [-69]) (l₂ := [-70])
  have hm := merge_right (literal (valuationOf q) (-70)) (literal (valuationOf q) (1504)) (countLit q [-69]) (countLit q [-70]) (count1504 q) 1 (meaningNeg70 q) (meaning1504 q) hs
  change (! (valuationOf q 70)) = false ∨ valuationOf q 1504 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause939 (q : Snake 81) (h : Conditions q) : valuation q 70 = true ∨ valuation q 1504 = true := counterClause939 (baseVal q)

theorem counterClause940 (q : Nat → Bool) : valuationOf q 1502 = false ∨ valuationOf q 1506 = true := by
  have hs : count1506 q = (countLit q [-66, -68]) + (countLit q [-69, -70]) := List.countP_append (p := literal q) (l₁ := [-66, -68]) (l₂ := [-69, -70])
  have hm := merge_left (literal (valuationOf q) (1502)) (literal (valuationOf q) (1506)) (countLit q [-66, -68]) (countLit q [-69, -70]) (count1506 q) 1 (meaning1502 q) (meaning1506 q) hs
  change valuationOf q 1502 = false ∨ valuationOf q 1506 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause940 (q : Snake 81) (h : Conditions q) : valuation q 1502 = false ∨ valuation q 1506 = true := counterClause940 (baseVal q)

theorem counterClause941 (q : Nat → Bool) : valuationOf q 1502 = false ∨ valuationOf q 1504 = false ∨ valuationOf q 1507 = true := by
  have hs : count1506 q = (countLit q [-66, -68]) + (countLit q [-69, -70]) := List.countP_append (p := literal q) (l₁ := [-66, -68]) (l₂ := [-69, -70])
  have hm := merge_two (literal (valuationOf q) (1502)) (literal (valuationOf q) (1504)) (literal (valuationOf q) (1507)) (countLit q [-66, -68]) (countLit q [-69, -70]) (count1506 q) 1 1 (meaning1502 q) (meaning1504 q) (meaning1507 q) hs
  change valuationOf q 1502 = false ∨ valuationOf q 1504 = false ∨ valuationOf q 1507 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause941 (q : Snake 81) (h : Conditions q) : valuation q 1502 = false ∨ valuation q 1504 = false ∨ valuation q 1507 = true := counterClause941 (baseVal q)

theorem counterClause942 (q : Nat → Bool) : valuationOf q 1503 = false ∨ valuationOf q 1507 = true := by
  have hs : count1506 q = (countLit q [-66, -68]) + (countLit q [-69, -70]) := List.countP_append (p := literal q) (l₁ := [-66, -68]) (l₂ := [-69, -70])
  have hm := merge_left (literal (valuationOf q) (1503)) (literal (valuationOf q) (1507)) (countLit q [-66, -68]) (countLit q [-69, -70]) (count1506 q) 2 (meaning1503 q) (meaning1507 q) hs
  change valuationOf q 1503 = false ∨ valuationOf q 1507 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause942 (q : Snake 81) (h : Conditions q) : valuation q 1503 = false ∨ valuation q 1507 = true := counterClause942 (baseVal q)

theorem counterClause943 (q : Nat → Bool) : valuationOf q 1503 = false ∨ valuationOf q 1504 = false ∨ valuationOf q 1508 = true := by
  have hs : count1506 q = (countLit q [-66, -68]) + (countLit q [-69, -70]) := List.countP_append (p := literal q) (l₁ := [-66, -68]) (l₂ := [-69, -70])
  have hm := merge_two (literal (valuationOf q) (1503)) (literal (valuationOf q) (1504)) (literal (valuationOf q) (1508)) (countLit q [-66, -68]) (countLit q [-69, -70]) (count1506 q) 2 1 (meaning1503 q) (meaning1504 q) (meaning1508 q) hs
  change valuationOf q 1503 = false ∨ valuationOf q 1504 = false ∨ valuationOf q 1508 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause943 (q : Snake 81) (h : Conditions q) : valuation q 1503 = false ∨ valuation q 1504 = false ∨ valuation q 1508 = true := counterClause943 (baseVal q)

theorem counterClause944 (q : Nat → Bool) : valuationOf q 1506 = false ∨ valuationOf q 1510 = true := by
  have hs : count1510 q = (countLit q [-60, -61, -62]) + (countLit q [-66, -68, -69, -70]) := List.countP_append (p := literal q) (l₁ := [-60, -61, -62]) (l₂ := [-66, -68, -69, -70])
  have hm := merge_right (literal (valuationOf q) (1506)) (literal (valuationOf q) (1510)) (countLit q [-60, -61, -62]) (countLit q [-66, -68, -69, -70]) (count1510 q) 1 (meaning1506 q) (meaning1510 q) hs
  change valuationOf q 1506 = false ∨ valuationOf q 1510 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause944 (q : Snake 81) (h : Conditions q) : valuation q 1506 = false ∨ valuation q 1510 = true := counterClause944 (baseVal q)

theorem counterClause945 (q : Nat → Bool) : valuationOf q 1507 = false ∨ valuationOf q 1511 = true := by
  have hs : count1510 q = (countLit q [-60, -61, -62]) + (countLit q [-66, -68, -69, -70]) := List.countP_append (p := literal q) (l₁ := [-60, -61, -62]) (l₂ := [-66, -68, -69, -70])
  have hm := merge_right (literal (valuationOf q) (1507)) (literal (valuationOf q) (1511)) (countLit q [-60, -61, -62]) (countLit q [-66, -68, -69, -70]) (count1510 q) 2 (meaning1507 q) (meaning1511 q) hs
  change valuationOf q 1507 = false ∨ valuationOf q 1511 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause945 (q : Snake 81) (h : Conditions q) : valuation q 1507 = false ∨ valuation q 1511 = true := counterClause945 (baseVal q)

theorem counterClause946 (q : Nat → Bool) : valuationOf q 1508 = false ∨ valuationOf q 1512 = true := by
  have hs : count1510 q = (countLit q [-60, -61, -62]) + (countLit q [-66, -68, -69, -70]) := List.countP_append (p := literal q) (l₁ := [-60, -61, -62]) (l₂ := [-66, -68, -69, -70])
  have hm := merge_right (literal (valuationOf q) (1508)) (literal (valuationOf q) (1512)) (countLit q [-60, -61, -62]) (countLit q [-66, -68, -69, -70]) (count1510 q) 3 (meaning1508 q) (meaning1512 q) hs
  change valuationOf q 1508 = false ∨ valuationOf q 1512 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause946 (q : Snake 81) (h : Conditions q) : valuation q 1508 = false ∨ valuation q 1512 = true := counterClause946 (baseVal q)

theorem counterClause947 (q : Nat → Bool) : valuationOf q 1499 = false ∨ valuationOf q 1506 = false ∨ valuationOf q 1511 = true := by
  have hs : count1510 q = (countLit q [-60, -61, -62]) + (countLit q [-66, -68, -69, -70]) := List.countP_append (p := literal q) (l₁ := [-60, -61, -62]) (l₂ := [-66, -68, -69, -70])
  have hm := merge_two (literal (valuationOf q) (1499)) (literal (valuationOf q) (1506)) (literal (valuationOf q) (1511)) (countLit q [-60, -61, -62]) (countLit q [-66, -68, -69, -70]) (count1510 q) 1 1 (meaning1499 q) (meaning1506 q) (meaning1511 q) hs
  change valuationOf q 1499 = false ∨ valuationOf q 1506 = false ∨ valuationOf q 1511 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause947 (q : Snake 81) (h : Conditions q) : valuation q 1499 = false ∨ valuation q 1506 = false ∨ valuation q 1511 = true := counterClause947 (baseVal q)

theorem counterClause948 (q : Nat → Bool) : valuationOf q 1499 = false ∨ valuationOf q 1507 = false ∨ valuationOf q 1512 = true := by
  have hs : count1510 q = (countLit q [-60, -61, -62]) + (countLit q [-66, -68, -69, -70]) := List.countP_append (p := literal q) (l₁ := [-60, -61, -62]) (l₂ := [-66, -68, -69, -70])
  have hm := merge_two (literal (valuationOf q) (1499)) (literal (valuationOf q) (1507)) (literal (valuationOf q) (1512)) (countLit q [-60, -61, -62]) (countLit q [-66, -68, -69, -70]) (count1510 q) 1 2 (meaning1499 q) (meaning1507 q) (meaning1512 q) hs
  change valuationOf q 1499 = false ∨ valuationOf q 1507 = false ∨ valuationOf q 1512 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause948 (q : Snake 81) (h : Conditions q) : valuation q 1499 = false ∨ valuation q 1507 = false ∨ valuation q 1512 = true := counterClause948 (baseVal q)

theorem counterClause949 (q : Nat → Bool) : valuationOf q 1499 = false ∨ valuationOf q 1508 = false ∨ valuationOf q 1513 = true := by
  have hs : count1510 q = (countLit q [-60, -61, -62]) + (countLit q [-66, -68, -69, -70]) := List.countP_append (p := literal q) (l₁ := [-60, -61, -62]) (l₂ := [-66, -68, -69, -70])
  have hm := merge_two (literal (valuationOf q) (1499)) (literal (valuationOf q) (1508)) (literal (valuationOf q) (1513)) (countLit q [-60, -61, -62]) (countLit q [-66, -68, -69, -70]) (count1510 q) 1 3 (meaning1499 q) (meaning1508 q) (meaning1513 q) hs
  change valuationOf q 1499 = false ∨ valuationOf q 1508 = false ∨ valuationOf q 1513 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause949 (q : Snake 81) (h : Conditions q) : valuation q 1499 = false ∨ valuation q 1508 = false ∨ valuation q 1513 = true := counterClause949 (baseVal q)

theorem counterClause950 (q : Nat → Bool) : valuationOf q 1500 = false ∨ valuationOf q 1511 = true := by
  have hs : count1510 q = (countLit q [-60, -61, -62]) + (countLit q [-66, -68, -69, -70]) := List.countP_append (p := literal q) (l₁ := [-60, -61, -62]) (l₂ := [-66, -68, -69, -70])
  have hm := merge_left (literal (valuationOf q) (1500)) (literal (valuationOf q) (1511)) (countLit q [-60, -61, -62]) (countLit q [-66, -68, -69, -70]) (count1510 q) 2 (meaning1500 q) (meaning1511 q) hs
  change valuationOf q 1500 = false ∨ valuationOf q 1511 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause950 (q : Snake 81) (h : Conditions q) : valuation q 1500 = false ∨ valuation q 1511 = true := counterClause950 (baseVal q)

theorem counterClause951 (q : Nat → Bool) : valuationOf q 1500 = false ∨ valuationOf q 1506 = false ∨ valuationOf q 1512 = true := by
  have hs : count1510 q = (countLit q [-60, -61, -62]) + (countLit q [-66, -68, -69, -70]) := List.countP_append (p := literal q) (l₁ := [-60, -61, -62]) (l₂ := [-66, -68, -69, -70])
  have hm := merge_two (literal (valuationOf q) (1500)) (literal (valuationOf q) (1506)) (literal (valuationOf q) (1512)) (countLit q [-60, -61, -62]) (countLit q [-66, -68, -69, -70]) (count1510 q) 2 1 (meaning1500 q) (meaning1506 q) (meaning1512 q) hs
  change valuationOf q 1500 = false ∨ valuationOf q 1506 = false ∨ valuationOf q 1512 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause951 (q : Snake 81) (h : Conditions q) : valuation q 1500 = false ∨ valuation q 1506 = false ∨ valuation q 1512 = true := counterClause951 (baseVal q)

theorem counterClause952 (q : Nat → Bool) : valuationOf q 1500 = false ∨ valuationOf q 1507 = false ∨ valuationOf q 1513 = true := by
  have hs : count1510 q = (countLit q [-60, -61, -62]) + (countLit q [-66, -68, -69, -70]) := List.countP_append (p := literal q) (l₁ := [-60, -61, -62]) (l₂ := [-66, -68, -69, -70])
  have hm := merge_two (literal (valuationOf q) (1500)) (literal (valuationOf q) (1507)) (literal (valuationOf q) (1513)) (countLit q [-60, -61, -62]) (countLit q [-66, -68, -69, -70]) (count1510 q) 2 2 (meaning1500 q) (meaning1507 q) (meaning1513 q) hs
  change valuationOf q 1500 = false ∨ valuationOf q 1507 = false ∨ valuationOf q 1513 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause952 (q : Snake 81) (h : Conditions q) : valuation q 1500 = false ∨ valuation q 1507 = false ∨ valuation q 1513 = true := counterClause952 (baseVal q)

theorem counterClause953 (q : Nat → Bool) : valuationOf q 1500 = false ∨ valuationOf q 1508 = false ∨ valuationOf q 1514 = true := by
  have hs : count1510 q = (countLit q [-60, -61, -62]) + (countLit q [-66, -68, -69, -70]) := List.countP_append (p := literal q) (l₁ := [-60, -61, -62]) (l₂ := [-66, -68, -69, -70])
  have hm := merge_two (literal (valuationOf q) (1500)) (literal (valuationOf q) (1508)) (literal (valuationOf q) (1514)) (countLit q [-60, -61, -62]) (countLit q [-66, -68, -69, -70]) (count1510 q) 2 3 (meaning1500 q) (meaning1508 q) (meaning1514 q) hs
  change valuationOf q 1500 = false ∨ valuationOf q 1508 = false ∨ valuationOf q 1514 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause953 (q : Snake 81) (h : Conditions q) : valuation q 1500 = false ∨ valuation q 1508 = false ∨ valuation q 1514 = true := counterClause953 (baseVal q)

theorem counterClause954 (q : Nat → Bool) : valuationOf q 1501 = false ∨ valuationOf q 1512 = true := by
  have hs : count1510 q = (countLit q [-60, -61, -62]) + (countLit q [-66, -68, -69, -70]) := List.countP_append (p := literal q) (l₁ := [-60, -61, -62]) (l₂ := [-66, -68, -69, -70])
  have hm := merge_left (literal (valuationOf q) (1501)) (literal (valuationOf q) (1512)) (countLit q [-60, -61, -62]) (countLit q [-66, -68, -69, -70]) (count1510 q) 3 (meaning1501 q) (meaning1512 q) hs
  change valuationOf q 1501 = false ∨ valuationOf q 1512 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause954 (q : Snake 81) (h : Conditions q) : valuation q 1501 = false ∨ valuation q 1512 = true := counterClause954 (baseVal q)

theorem counterClause955 (q : Nat → Bool) : valuationOf q 1501 = false ∨ valuationOf q 1506 = false ∨ valuationOf q 1513 = true := by
  have hs : count1510 q = (countLit q [-60, -61, -62]) + (countLit q [-66, -68, -69, -70]) := List.countP_append (p := literal q) (l₁ := [-60, -61, -62]) (l₂ := [-66, -68, -69, -70])
  have hm := merge_two (literal (valuationOf q) (1501)) (literal (valuationOf q) (1506)) (literal (valuationOf q) (1513)) (countLit q [-60, -61, -62]) (countLit q [-66, -68, -69, -70]) (count1510 q) 3 1 (meaning1501 q) (meaning1506 q) (meaning1513 q) hs
  change valuationOf q 1501 = false ∨ valuationOf q 1506 = false ∨ valuationOf q 1513 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause955 (q : Snake 81) (h : Conditions q) : valuation q 1501 = false ∨ valuation q 1506 = false ∨ valuation q 1513 = true := counterClause955 (baseVal q)

theorem counterClause956 (q : Nat → Bool) : valuationOf q 1501 = false ∨ valuationOf q 1507 = false ∨ valuationOf q 1514 = true := by
  have hs : count1510 q = (countLit q [-60, -61, -62]) + (countLit q [-66, -68, -69, -70]) := List.countP_append (p := literal q) (l₁ := [-60, -61, -62]) (l₂ := [-66, -68, -69, -70])
  have hm := merge_two (literal (valuationOf q) (1501)) (literal (valuationOf q) (1507)) (literal (valuationOf q) (1514)) (countLit q [-60, -61, -62]) (countLit q [-66, -68, -69, -70]) (count1510 q) 3 2 (meaning1501 q) (meaning1507 q) (meaning1514 q) hs
  change valuationOf q 1501 = false ∨ valuationOf q 1507 = false ∨ valuationOf q 1514 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause956 (q : Snake 81) (h : Conditions q) : valuation q 1501 = false ∨ valuation q 1507 = false ∨ valuation q 1514 = true := counterClause956 (baseVal q)

theorem counterClause957 (q : Nat → Bool) : valuationOf q 1501 = false ∨ valuationOf q 1508 = false ∨ valuationOf q 1515 = true := by
  have hs : count1510 q = (countLit q [-60, -61, -62]) + (countLit q [-66, -68, -69, -70]) := List.countP_append (p := literal q) (l₁ := [-60, -61, -62]) (l₂ := [-66, -68, -69, -70])
  have hm := merge_two (literal (valuationOf q) (1501)) (literal (valuationOf q) (1508)) (literal (valuationOf q) (1515)) (countLit q [-60, -61, -62]) (countLit q [-66, -68, -69, -70]) (count1510 q) 3 3 (meaning1501 q) (meaning1508 q) (meaning1515 q) hs
  change valuationOf q 1501 = false ∨ valuationOf q 1508 = false ∨ valuationOf q 1515 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause957 (q : Snake 81) (h : Conditions q) : valuation q 1501 = false ∨ valuation q 1508 = false ∨ valuation q 1515 = true := counterClause957 (baseVal q)

theorem counterClause958 (q : Nat → Bool) : valuationOf q 77 = true ∨ valuationOf q 1517 = true := by
  have hs : count1517 q = (countLit q [-76]) + (countLit q [-77]) := List.countP_append (p := literal q) (l₁ := [-76]) (l₂ := [-77])
  have hm := merge_right (literal (valuationOf q) (-77)) (literal (valuationOf q) (1517)) (countLit q [-76]) (countLit q [-77]) (count1517 q) 1 (meaningNeg77 q) (meaning1517 q) hs
  change (! (valuationOf q 77)) = false ∨ valuationOf q 1517 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause958 (q : Snake 81) (h : Conditions q) : valuation q 77 = true ∨ valuation q 1517 = true := counterClause958 (baseVal q)

theorem counterClause959 (q : Nat → Bool) : valuationOf q 76 = true ∨ valuationOf q 1517 = true := by
  have hs : count1517 q = (countLit q [-76]) + (countLit q [-77]) := List.countP_append (p := literal q) (l₁ := [-76]) (l₂ := [-77])
  have hm := merge_left (literal (valuationOf q) (-76)) (literal (valuationOf q) (1517)) (countLit q [-76]) (countLit q [-77]) (count1517 q) 1 (meaningNeg76 q) (meaning1517 q) hs
  change (! (valuationOf q 76)) = false ∨ valuationOf q 1517 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause959 (q : Snake 81) (h : Conditions q) : valuation q 76 = true ∨ valuation q 1517 = true := counterClause959 (baseVal q)

theorem counterClause960 (q : Nat → Bool) : valuationOf q 76 = true ∨ valuationOf q 77 = true ∨ valuationOf q 1518 = true := by
  have hs : count1517 q = (countLit q [-76]) + (countLit q [-77]) := List.countP_append (p := literal q) (l₁ := [-76]) (l₂ := [-77])
  have hm := merge_two (literal (valuationOf q) (-76)) (literal (valuationOf q) (-77)) (literal (valuationOf q) (1518)) (countLit q [-76]) (countLit q [-77]) (count1517 q) 1 1 (meaningNeg76 q) (meaningNeg77 q) (meaning1518 q) hs
  change (! (valuationOf q 76)) = false ∨ (! (valuationOf q 77)) = false ∨ valuationOf q 1518 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause960 (q : Snake 81) (h : Conditions q) : valuation q 76 = true ∨ valuation q 77 = true ∨ valuation q 1518 = true := counterClause960 (baseVal q)

theorem block29 (q : Snake 81) (h : Conditions q) : B112E168.Block29 (valuation q) :=
  ⟨clause929 q h, clause930 q h, clause931 q h, clause932 q h, clause933 q h, clause934 q h, clause935 q h, clause936 q h, clause937 q h, clause938 q h, clause939 q h, clause940 q h, clause941 q h, clause942 q h, clause943 q h, clause944 q h, clause945 q h, clause946 q h, clause947 q h, clause948 q h, clause949 q h, clause950 q h, clause951 q h, clause952 q h, clause953 q h, clause954 q h, clause955 q h, clause956 q h, clause957 q h, clause958 q h, clause959 q h, clause960 q h⟩

end
end Snake9.Regrowth.E112168
