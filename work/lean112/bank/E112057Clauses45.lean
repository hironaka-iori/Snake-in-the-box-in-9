import E112057Semantics
import B112E057Inputs
namespace Snake9.Regrowth.E112057
noncomputable section
local instance blockDec45 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1441 (q : Nat → Bool) : valuationOf q 54 = true ∨ valuationOf q 957 = true := by
  have hs : count957 q = (countLit q [-54]) + (countLit q [-56]) := List.countP_append (p := literal q) (l₁ := [-54]) (l₂ := [-56])
  have hm := merge_left (literal (valuationOf q) (-54)) (literal (valuationOf q) (957)) (countLit q [-54]) (countLit q [-56]) (count957 q) 1 (meaningNeg54 q) (meaning957 q) hs
  change (! (valuationOf q 54)) = false ∨ valuationOf q 957 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1441 (q : Snake 81) (h : Conditions q) : valuation q 54 = true ∨ valuation q 957 = true := counterClause1441 (baseVal q)

theorem counterClause1442 (q : Nat → Bool) : valuationOf q 54 = true ∨ valuationOf q 56 = true ∨ valuationOf q 958 = true := by
  have hs : count957 q = (countLit q [-54]) + (countLit q [-56]) := List.countP_append (p := literal q) (l₁ := [-54]) (l₂ := [-56])
  have hm := merge_two (literal (valuationOf q) (-54)) (literal (valuationOf q) (-56)) (literal (valuationOf q) (958)) (countLit q [-54]) (countLit q [-56]) (count957 q) 1 1 (meaningNeg54 q) (meaningNeg56 q) (meaning958 q) hs
  change (! (valuationOf q 54)) = false ∨ (! (valuationOf q 56)) = false ∨ valuationOf q 958 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1442 (q : Snake 81) (h : Conditions q) : valuation q 54 = true ∨ valuation q 56 = true ∨ valuation q 958 = true := counterClause1442 (baseVal q)

theorem counterClause1443 (q : Nat → Bool) : valuationOf q 957 = false ∨ valuationOf q 959 = true := by
  have hs : count959 q = (countLit q [-50, -51]) + (countLit q [-54, -56]) := List.countP_append (p := literal q) (l₁ := [-50, -51]) (l₂ := [-54, -56])
  have hm := merge_right (literal (valuationOf q) (957)) (literal (valuationOf q) (959)) (countLit q [-50, -51]) (countLit q [-54, -56]) (count959 q) 1 (meaning957 q) (meaning959 q) hs
  change valuationOf q 957 = false ∨ valuationOf q 959 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1443 (q : Snake 81) (h : Conditions q) : valuation q 957 = false ∨ valuation q 959 = true := counterClause1443 (baseVal q)

theorem counterClause1444 (q : Nat → Bool) : valuationOf q 958 = false ∨ valuationOf q 960 = true := by
  have hs : count959 q = (countLit q [-50, -51]) + (countLit q [-54, -56]) := List.countP_append (p := literal q) (l₁ := [-50, -51]) (l₂ := [-54, -56])
  have hm := merge_right (literal (valuationOf q) (958)) (literal (valuationOf q) (960)) (countLit q [-50, -51]) (countLit q [-54, -56]) (count959 q) 2 (meaning958 q) (meaning960 q) hs
  change valuationOf q 958 = false ∨ valuationOf q 960 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1444 (q : Snake 81) (h : Conditions q) : valuation q 958 = false ∨ valuation q 960 = true := counterClause1444 (baseVal q)

theorem counterClause1445 (q : Nat → Bool) : valuationOf q 955 = false ∨ valuationOf q 959 = true := by
  have hs : count959 q = (countLit q [-50, -51]) + (countLit q [-54, -56]) := List.countP_append (p := literal q) (l₁ := [-50, -51]) (l₂ := [-54, -56])
  have hm := merge_left (literal (valuationOf q) (955)) (literal (valuationOf q) (959)) (countLit q [-50, -51]) (countLit q [-54, -56]) (count959 q) 1 (meaning955 q) (meaning959 q) hs
  change valuationOf q 955 = false ∨ valuationOf q 959 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1445 (q : Snake 81) (h : Conditions q) : valuation q 955 = false ∨ valuation q 959 = true := counterClause1445 (baseVal q)

theorem counterClause1446 (q : Nat → Bool) : valuationOf q 955 = false ∨ valuationOf q 957 = false ∨ valuationOf q 960 = true := by
  have hs : count959 q = (countLit q [-50, -51]) + (countLit q [-54, -56]) := List.countP_append (p := literal q) (l₁ := [-50, -51]) (l₂ := [-54, -56])
  have hm := merge_two (literal (valuationOf q) (955)) (literal (valuationOf q) (957)) (literal (valuationOf q) (960)) (countLit q [-50, -51]) (countLit q [-54, -56]) (count959 q) 1 1 (meaning955 q) (meaning957 q) (meaning960 q) hs
  change valuationOf q 955 = false ∨ valuationOf q 957 = false ∨ valuationOf q 960 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1446 (q : Snake 81) (h : Conditions q) : valuation q 955 = false ∨ valuation q 957 = false ∨ valuation q 960 = true := counterClause1446 (baseVal q)

theorem counterClause1447 (q : Nat → Bool) : valuationOf q 955 = false ∨ valuationOf q 958 = false ∨ valuationOf q 961 = true := by
  have hs : count959 q = (countLit q [-50, -51]) + (countLit q [-54, -56]) := List.countP_append (p := literal q) (l₁ := [-50, -51]) (l₂ := [-54, -56])
  have hm := merge_two (literal (valuationOf q) (955)) (literal (valuationOf q) (958)) (literal (valuationOf q) (961)) (countLit q [-50, -51]) (countLit q [-54, -56]) (count959 q) 1 2 (meaning955 q) (meaning958 q) (meaning961 q) hs
  change valuationOf q 955 = false ∨ valuationOf q 958 = false ∨ valuationOf q 961 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1447 (q : Snake 81) (h : Conditions q) : valuation q 955 = false ∨ valuation q 958 = false ∨ valuation q 961 = true := counterClause1447 (baseVal q)

theorem counterClause1448 (q : Nat → Bool) : valuationOf q 956 = false ∨ valuationOf q 960 = true := by
  have hs : count959 q = (countLit q [-50, -51]) + (countLit q [-54, -56]) := List.countP_append (p := literal q) (l₁ := [-50, -51]) (l₂ := [-54, -56])
  have hm := merge_left (literal (valuationOf q) (956)) (literal (valuationOf q) (960)) (countLit q [-50, -51]) (countLit q [-54, -56]) (count959 q) 2 (meaning956 q) (meaning960 q) hs
  change valuationOf q 956 = false ∨ valuationOf q 960 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1448 (q : Snake 81) (h : Conditions q) : valuation q 956 = false ∨ valuation q 960 = true := counterClause1448 (baseVal q)

theorem counterClause1449 (q : Nat → Bool) : valuationOf q 956 = false ∨ valuationOf q 957 = false ∨ valuationOf q 961 = true := by
  have hs : count959 q = (countLit q [-50, -51]) + (countLit q [-54, -56]) := List.countP_append (p := literal q) (l₁ := [-50, -51]) (l₂ := [-54, -56])
  have hm := merge_two (literal (valuationOf q) (956)) (literal (valuationOf q) (957)) (literal (valuationOf q) (961)) (countLit q [-50, -51]) (countLit q [-54, -56]) (count959 q) 2 1 (meaning956 q) (meaning957 q) (meaning961 q) hs
  change valuationOf q 956 = false ∨ valuationOf q 957 = false ∨ valuationOf q 961 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1449 (q : Snake 81) (h : Conditions q) : valuation q 956 = false ∨ valuation q 957 = false ∨ valuation q 961 = true := counterClause1449 (baseVal q)

theorem counterClause1450 (q : Nat → Bool) : valuationOf q 956 = false ∨ valuationOf q 958 = false ∨ valuationOf q 962 = true := by
  have hs : count959 q = (countLit q [-50, -51]) + (countLit q [-54, -56]) := List.countP_append (p := literal q) (l₁ := [-50, -51]) (l₂ := [-54, -56])
  have hm := merge_two (literal (valuationOf q) (956)) (literal (valuationOf q) (958)) (literal (valuationOf q) (962)) (countLit q [-50, -51]) (countLit q [-54, -56]) (count959 q) 2 2 (meaning956 q) (meaning958 q) (meaning962 q) hs
  change valuationOf q 956 = false ∨ valuationOf q 958 = false ∨ valuationOf q 962 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1450 (q : Snake 81) (h : Conditions q) : valuation q 956 = false ∨ valuation q 958 = false ∨ valuation q 962 = true := counterClause1450 (baseVal q)

theorem counterClause1451 (q : Nat → Bool) : valuationOf q 60 = true ∨ valuationOf q 963 = true := by
  have hs : count963 q = (countLit q [-59]) + (countLit q [-60]) := List.countP_append (p := literal q) (l₁ := [-59]) (l₂ := [-60])
  have hm := merge_right (literal (valuationOf q) (-60)) (literal (valuationOf q) (963)) (countLit q [-59]) (countLit q [-60]) (count963 q) 1 (meaningNeg60 q) (meaning963 q) hs
  change (! (valuationOf q 60)) = false ∨ valuationOf q 963 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1451 (q : Snake 81) (h : Conditions q) : valuation q 60 = true ∨ valuation q 963 = true := counterClause1451 (baseVal q)

theorem counterClause1452 (q : Nat → Bool) : valuationOf q 59 = true ∨ valuationOf q 963 = true := by
  have hs : count963 q = (countLit q [-59]) + (countLit q [-60]) := List.countP_append (p := literal q) (l₁ := [-59]) (l₂ := [-60])
  have hm := merge_left (literal (valuationOf q) (-59)) (literal (valuationOf q) (963)) (countLit q [-59]) (countLit q [-60]) (count963 q) 1 (meaningNeg59 q) (meaning963 q) hs
  change (! (valuationOf q 59)) = false ∨ valuationOf q 963 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1452 (q : Snake 81) (h : Conditions q) : valuation q 59 = true ∨ valuation q 963 = true := counterClause1452 (baseVal q)

theorem counterClause1453 (q : Nat → Bool) : valuationOf q 59 = true ∨ valuationOf q 60 = true ∨ valuationOf q 964 = true := by
  have hs : count963 q = (countLit q [-59]) + (countLit q [-60]) := List.countP_append (p := literal q) (l₁ := [-59]) (l₂ := [-60])
  have hm := merge_two (literal (valuationOf q) (-59)) (literal (valuationOf q) (-60)) (literal (valuationOf q) (964)) (countLit q [-59]) (countLit q [-60]) (count963 q) 1 1 (meaningNeg59 q) (meaningNeg60 q) (meaning964 q) hs
  change (! (valuationOf q 59)) = false ∨ (! (valuationOf q 60)) = false ∨ valuationOf q 964 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1453 (q : Snake 81) (h : Conditions q) : valuation q 59 = true ∨ valuation q 60 = true ∨ valuation q 964 = true := counterClause1453 (baseVal q)

theorem counterClause1454 (q : Nat → Bool) : valuationOf q 61 = true ∨ valuationOf q 965 = true := by
  have hs : count965 q = (countLit q [-61]) + (countLit q [-64]) := List.countP_append (p := literal q) (l₁ := [-61]) (l₂ := [-64])
  have hm := merge_left (literal (valuationOf q) (-61)) (literal (valuationOf q) (965)) (countLit q [-61]) (countLit q [-64]) (count965 q) 1 (meaningNeg61 q) (meaning965 q) hs
  change (! (valuationOf q 61)) = false ∨ valuationOf q 965 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1454 (q : Snake 81) (h : Conditions q) : valuation q 61 = true ∨ valuation q 965 = true := counterClause1454 (baseVal q)

theorem counterClause1455 (q : Nat → Bool) : valuationOf q 61 = true ∨ valuationOf q 64 = true ∨ valuationOf q 966 = true := by
  have hs : count965 q = (countLit q [-61]) + (countLit q [-64]) := List.countP_append (p := literal q) (l₁ := [-61]) (l₂ := [-64])
  have hm := merge_two (literal (valuationOf q) (-61)) (literal (valuationOf q) (-64)) (literal (valuationOf q) (966)) (countLit q [-61]) (countLit q [-64]) (count965 q) 1 1 (meaningNeg61 q) (meaningNeg64 q) (meaning966 q) hs
  change (! (valuationOf q 61)) = false ∨ (! (valuationOf q 64)) = false ∨ valuationOf q 966 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1455 (q : Snake 81) (h : Conditions q) : valuation q 61 = true ∨ valuation q 64 = true ∨ valuation q 966 = true := counterClause1455 (baseVal q)

theorem counterClause1456 (q : Nat → Bool) : valuationOf q 965 = false ∨ valuationOf q 967 = true := by
  have hs : count967 q = (countLit q [-59, -60]) + (countLit q [-61, -64]) := List.countP_append (p := literal q) (l₁ := [-59, -60]) (l₂ := [-61, -64])
  have hm := merge_right (literal (valuationOf q) (965)) (literal (valuationOf q) (967)) (countLit q [-59, -60]) (countLit q [-61, -64]) (count967 q) 1 (meaning965 q) (meaning967 q) hs
  change valuationOf q 965 = false ∨ valuationOf q 967 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1456 (q : Snake 81) (h : Conditions q) : valuation q 965 = false ∨ valuation q 967 = true := counterClause1456 (baseVal q)

theorem counterClause1457 (q : Nat → Bool) : valuationOf q 966 = false ∨ valuationOf q 968 = true := by
  have hs : count967 q = (countLit q [-59, -60]) + (countLit q [-61, -64]) := List.countP_append (p := literal q) (l₁ := [-59, -60]) (l₂ := [-61, -64])
  have hm := merge_right (literal (valuationOf q) (966)) (literal (valuationOf q) (968)) (countLit q [-59, -60]) (countLit q [-61, -64]) (count967 q) 2 (meaning966 q) (meaning968 q) hs
  change valuationOf q 966 = false ∨ valuationOf q 968 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1457 (q : Snake 81) (h : Conditions q) : valuation q 966 = false ∨ valuation q 968 = true := counterClause1457 (baseVal q)

theorem counterClause1458 (q : Nat → Bool) : valuationOf q 963 = false ∨ valuationOf q 965 = false ∨ valuationOf q 968 = true := by
  have hs : count967 q = (countLit q [-59, -60]) + (countLit q [-61, -64]) := List.countP_append (p := literal q) (l₁ := [-59, -60]) (l₂ := [-61, -64])
  have hm := merge_two (literal (valuationOf q) (963)) (literal (valuationOf q) (965)) (literal (valuationOf q) (968)) (countLit q [-59, -60]) (countLit q [-61, -64]) (count967 q) 1 1 (meaning963 q) (meaning965 q) (meaning968 q) hs
  change valuationOf q 963 = false ∨ valuationOf q 965 = false ∨ valuationOf q 968 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1458 (q : Snake 81) (h : Conditions q) : valuation q 963 = false ∨ valuation q 965 = false ∨ valuation q 968 = true := counterClause1458 (baseVal q)

theorem counterClause1459 (q : Nat → Bool) : valuationOf q 963 = false ∨ valuationOf q 966 = false ∨ valuationOf q 969 = true := by
  have hs : count967 q = (countLit q [-59, -60]) + (countLit q [-61, -64]) := List.countP_append (p := literal q) (l₁ := [-59, -60]) (l₂ := [-61, -64])
  have hm := merge_two (literal (valuationOf q) (963)) (literal (valuationOf q) (966)) (literal (valuationOf q) (969)) (countLit q [-59, -60]) (countLit q [-61, -64]) (count967 q) 1 2 (meaning963 q) (meaning966 q) (meaning969 q) hs
  change valuationOf q 963 = false ∨ valuationOf q 966 = false ∨ valuationOf q 969 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1459 (q : Snake 81) (h : Conditions q) : valuation q 963 = false ∨ valuation q 966 = false ∨ valuation q 969 = true := counterClause1459 (baseVal q)

theorem counterClause1460 (q : Nat → Bool) : valuationOf q 964 = false ∨ valuationOf q 965 = false ∨ valuationOf q 969 = true := by
  have hs : count967 q = (countLit q [-59, -60]) + (countLit q [-61, -64]) := List.countP_append (p := literal q) (l₁ := [-59, -60]) (l₂ := [-61, -64])
  have hm := merge_two (literal (valuationOf q) (964)) (literal (valuationOf q) (965)) (literal (valuationOf q) (969)) (countLit q [-59, -60]) (countLit q [-61, -64]) (count967 q) 2 1 (meaning964 q) (meaning965 q) (meaning969 q) hs
  change valuationOf q 964 = false ∨ valuationOf q 965 = false ∨ valuationOf q 969 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1460 (q : Snake 81) (h : Conditions q) : valuation q 964 = false ∨ valuation q 965 = false ∨ valuation q 969 = true := counterClause1460 (baseVal q)

theorem counterClause1461 (q : Nat → Bool) : valuationOf q 964 = false ∨ valuationOf q 966 = false ∨ valuationOf q 970 = true := by
  have hs : count967 q = (countLit q [-59, -60]) + (countLit q [-61, -64]) := List.countP_append (p := literal q) (l₁ := [-59, -60]) (l₂ := [-61, -64])
  have hm := merge_two (literal (valuationOf q) (964)) (literal (valuationOf q) (966)) (literal (valuationOf q) (970)) (countLit q [-59, -60]) (countLit q [-61, -64]) (count967 q) 2 2 (meaning964 q) (meaning966 q) (meaning970 q) hs
  change valuationOf q 964 = false ∨ valuationOf q 966 = false ∨ valuationOf q 970 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1461 (q : Snake 81) (h : Conditions q) : valuation q 964 = false ∨ valuation q 966 = false ∨ valuation q 970 = true := counterClause1461 (baseVal q)

theorem counterClause1462 (q : Nat → Bool) : valuationOf q 967 = false ∨ valuationOf q 971 = true := by
  have hs : count971 q = (countLit q [-50, -51, -54, -56]) + (countLit q [-59, -60, -61, -64]) := List.countP_append (p := literal q) (l₁ := [-50, -51, -54, -56]) (l₂ := [-59, -60, -61, -64])
  have hm := merge_right (literal (valuationOf q) (967)) (literal (valuationOf q) (971)) (countLit q [-50, -51, -54, -56]) (countLit q [-59, -60, -61, -64]) (count971 q) 1 (meaning967 q) (meaning971 q) hs
  change valuationOf q 967 = false ∨ valuationOf q 971 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1462 (q : Snake 81) (h : Conditions q) : valuation q 967 = false ∨ valuation q 971 = true := counterClause1462 (baseVal q)

theorem counterClause1463 (q : Nat → Bool) : valuationOf q 968 = false ∨ valuationOf q 972 = true := by
  have hs : count971 q = (countLit q [-50, -51, -54, -56]) + (countLit q [-59, -60, -61, -64]) := List.countP_append (p := literal q) (l₁ := [-50, -51, -54, -56]) (l₂ := [-59, -60, -61, -64])
  have hm := merge_right (literal (valuationOf q) (968)) (literal (valuationOf q) (972)) (countLit q [-50, -51, -54, -56]) (countLit q [-59, -60, -61, -64]) (count971 q) 2 (meaning968 q) (meaning972 q) hs
  change valuationOf q 968 = false ∨ valuationOf q 972 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1463 (q : Snake 81) (h : Conditions q) : valuation q 968 = false ∨ valuation q 972 = true := counterClause1463 (baseVal q)

theorem counterClause1464 (q : Nat → Bool) : valuationOf q 969 = false ∨ valuationOf q 973 = true := by
  have hs : count971 q = (countLit q [-50, -51, -54, -56]) + (countLit q [-59, -60, -61, -64]) := List.countP_append (p := literal q) (l₁ := [-50, -51, -54, -56]) (l₂ := [-59, -60, -61, -64])
  have hm := merge_right (literal (valuationOf q) (969)) (literal (valuationOf q) (973)) (countLit q [-50, -51, -54, -56]) (countLit q [-59, -60, -61, -64]) (count971 q) 3 (meaning969 q) (meaning973 q) hs
  change valuationOf q 969 = false ∨ valuationOf q 973 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1464 (q : Snake 81) (h : Conditions q) : valuation q 969 = false ∨ valuation q 973 = true := counterClause1464 (baseVal q)

theorem counterClause1465 (q : Nat → Bool) : valuationOf q 959 = false ∨ valuationOf q 967 = false ∨ valuationOf q 972 = true := by
  have hs : count971 q = (countLit q [-50, -51, -54, -56]) + (countLit q [-59, -60, -61, -64]) := List.countP_append (p := literal q) (l₁ := [-50, -51, -54, -56]) (l₂ := [-59, -60, -61, -64])
  have hm := merge_two (literal (valuationOf q) (959)) (literal (valuationOf q) (967)) (literal (valuationOf q) (972)) (countLit q [-50, -51, -54, -56]) (countLit q [-59, -60, -61, -64]) (count971 q) 1 1 (meaning959 q) (meaning967 q) (meaning972 q) hs
  change valuationOf q 959 = false ∨ valuationOf q 967 = false ∨ valuationOf q 972 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1465 (q : Snake 81) (h : Conditions q) : valuation q 959 = false ∨ valuation q 967 = false ∨ valuation q 972 = true := counterClause1465 (baseVal q)

theorem counterClause1466 (q : Nat → Bool) : valuationOf q 959 = false ∨ valuationOf q 968 = false ∨ valuationOf q 973 = true := by
  have hs : count971 q = (countLit q [-50, -51, -54, -56]) + (countLit q [-59, -60, -61, -64]) := List.countP_append (p := literal q) (l₁ := [-50, -51, -54, -56]) (l₂ := [-59, -60, -61, -64])
  have hm := merge_two (literal (valuationOf q) (959)) (literal (valuationOf q) (968)) (literal (valuationOf q) (973)) (countLit q [-50, -51, -54, -56]) (countLit q [-59, -60, -61, -64]) (count971 q) 1 2 (meaning959 q) (meaning968 q) (meaning973 q) hs
  change valuationOf q 959 = false ∨ valuationOf q 968 = false ∨ valuationOf q 973 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1466 (q : Snake 81) (h : Conditions q) : valuation q 959 = false ∨ valuation q 968 = false ∨ valuation q 973 = true := counterClause1466 (baseVal q)

theorem counterClause1467 (q : Nat → Bool) : valuationOf q 959 = false ∨ valuationOf q 969 = false ∨ valuationOf q 974 = true := by
  have hs : count971 q = (countLit q [-50, -51, -54, -56]) + (countLit q [-59, -60, -61, -64]) := List.countP_append (p := literal q) (l₁ := [-50, -51, -54, -56]) (l₂ := [-59, -60, -61, -64])
  have hm := merge_two (literal (valuationOf q) (959)) (literal (valuationOf q) (969)) (literal (valuationOf q) (974)) (countLit q [-50, -51, -54, -56]) (countLit q [-59, -60, -61, -64]) (count971 q) 1 3 (meaning959 q) (meaning969 q) (meaning974 q) hs
  change valuationOf q 959 = false ∨ valuationOf q 969 = false ∨ valuationOf q 974 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1467 (q : Snake 81) (h : Conditions q) : valuation q 959 = false ∨ valuation q 969 = false ∨ valuation q 974 = true := counterClause1467 (baseVal q)

theorem counterClause1468 (q : Nat → Bool) : valuationOf q 959 = false ∨ valuationOf q 970 = false ∨ valuationOf q 975 = true := by
  have hs : count971 q = (countLit q [-50, -51, -54, -56]) + (countLit q [-59, -60, -61, -64]) := List.countP_append (p := literal q) (l₁ := [-50, -51, -54, -56]) (l₂ := [-59, -60, -61, -64])
  have hm := merge_two (literal (valuationOf q) (959)) (literal (valuationOf q) (970)) (literal (valuationOf q) (975)) (countLit q [-50, -51, -54, -56]) (countLit q [-59, -60, -61, -64]) (count971 q) 1 4 (meaning959 q) (meaning970 q) (meaning975 q) hs
  change valuationOf q 959 = false ∨ valuationOf q 970 = false ∨ valuationOf q 975 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1468 (q : Snake 81) (h : Conditions q) : valuation q 959 = false ∨ valuation q 970 = false ∨ valuation q 975 = true := counterClause1468 (baseVal q)

theorem counterClause1469 (q : Nat → Bool) : valuationOf q 960 = false ∨ valuationOf q 972 = true := by
  have hs : count971 q = (countLit q [-50, -51, -54, -56]) + (countLit q [-59, -60, -61, -64]) := List.countP_append (p := literal q) (l₁ := [-50, -51, -54, -56]) (l₂ := [-59, -60, -61, -64])
  have hm := merge_left (literal (valuationOf q) (960)) (literal (valuationOf q) (972)) (countLit q [-50, -51, -54, -56]) (countLit q [-59, -60, -61, -64]) (count971 q) 2 (meaning960 q) (meaning972 q) hs
  change valuationOf q 960 = false ∨ valuationOf q 972 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1469 (q : Snake 81) (h : Conditions q) : valuation q 960 = false ∨ valuation q 972 = true := counterClause1469 (baseVal q)

theorem counterClause1470 (q : Nat → Bool) : valuationOf q 960 = false ∨ valuationOf q 967 = false ∨ valuationOf q 973 = true := by
  have hs : count971 q = (countLit q [-50, -51, -54, -56]) + (countLit q [-59, -60, -61, -64]) := List.countP_append (p := literal q) (l₁ := [-50, -51, -54, -56]) (l₂ := [-59, -60, -61, -64])
  have hm := merge_two (literal (valuationOf q) (960)) (literal (valuationOf q) (967)) (literal (valuationOf q) (973)) (countLit q [-50, -51, -54, -56]) (countLit q [-59, -60, -61, -64]) (count971 q) 2 1 (meaning960 q) (meaning967 q) (meaning973 q) hs
  change valuationOf q 960 = false ∨ valuationOf q 967 = false ∨ valuationOf q 973 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1470 (q : Snake 81) (h : Conditions q) : valuation q 960 = false ∨ valuation q 967 = false ∨ valuation q 973 = true := counterClause1470 (baseVal q)

theorem counterClause1471 (q : Nat → Bool) : valuationOf q 960 = false ∨ valuationOf q 968 = false ∨ valuationOf q 974 = true := by
  have hs : count971 q = (countLit q [-50, -51, -54, -56]) + (countLit q [-59, -60, -61, -64]) := List.countP_append (p := literal q) (l₁ := [-50, -51, -54, -56]) (l₂ := [-59, -60, -61, -64])
  have hm := merge_two (literal (valuationOf q) (960)) (literal (valuationOf q) (968)) (literal (valuationOf q) (974)) (countLit q [-50, -51, -54, -56]) (countLit q [-59, -60, -61, -64]) (count971 q) 2 2 (meaning960 q) (meaning968 q) (meaning974 q) hs
  change valuationOf q 960 = false ∨ valuationOf q 968 = false ∨ valuationOf q 974 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1471 (q : Snake 81) (h : Conditions q) : valuation q 960 = false ∨ valuation q 968 = false ∨ valuation q 974 = true := counterClause1471 (baseVal q)

theorem counterClause1472 (q : Nat → Bool) : valuationOf q 960 = false ∨ valuationOf q 969 = false ∨ valuationOf q 975 = true := by
  have hs : count971 q = (countLit q [-50, -51, -54, -56]) + (countLit q [-59, -60, -61, -64]) := List.countP_append (p := literal q) (l₁ := [-50, -51, -54, -56]) (l₂ := [-59, -60, -61, -64])
  have hm := merge_two (literal (valuationOf q) (960)) (literal (valuationOf q) (969)) (literal (valuationOf q) (975)) (countLit q [-50, -51, -54, -56]) (countLit q [-59, -60, -61, -64]) (count971 q) 2 3 (meaning960 q) (meaning969 q) (meaning975 q) hs
  change valuationOf q 960 = false ∨ valuationOf q 969 = false ∨ valuationOf q 975 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1472 (q : Snake 81) (h : Conditions q) : valuation q 960 = false ∨ valuation q 969 = false ∨ valuation q 975 = true := counterClause1472 (baseVal q)

theorem block45 (q : Snake 81) (h : Conditions q) : B112E057.Block45 (valuation q) :=
  ⟨clause1441 q h, clause1442 q h, clause1443 q h, clause1444 q h, clause1445 q h, clause1446 q h, clause1447 q h, clause1448 q h, clause1449 q h, clause1450 q h, clause1451 q h, clause1452 q h, clause1453 q h, clause1454 q h, clause1455 q h, clause1456 q h, clause1457 q h, clause1458 q h, clause1459 q h, clause1460 q h, clause1461 q h, clause1462 q h, clause1463 q h, clause1464 q h, clause1465 q h, clause1466 q h, clause1467 q h, clause1468 q h, clause1469 q h, clause1470 q h, clause1471 q h, clause1472 q h⟩

end
end Snake9.Regrowth.E112057
