import E112121Semantics
import B112E121Inputs
namespace Snake9.Regrowth.E112121
noncomputable section
local instance blockDec40 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1281 (q : Nat → Bool) : valuationOf q 952 = false ∨ valuationOf q 954 = false ∨ valuationOf q 958 = true := by
  have hs : count955 q = (countLit q [-46, -47]) + (countLit q [-51, -53]) := List.countP_append (p := literal q) (l₁ := [-46, -47]) (l₂ := [-51, -53])
  have hm := merge_two (literal (valuationOf q) (952)) (literal (valuationOf q) (954)) (literal (valuationOf q) (958)) (countLit q [-46, -47]) (countLit q [-51, -53]) (count955 q) 2 2 (meaning952 q) (meaning954 q) (meaning958 q) hs
  change valuationOf q 952 = false ∨ valuationOf q 954 = false ∨ valuationOf q 958 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1281 (q : Snake 81) (h : Conditions q) : valuation q 952 = false ∨ valuation q 954 = false ∨ valuation q 958 = true := counterClause1281 (baseVal q)

theorem counterClause1282 (q : Nat → Bool) : valuationOf q 57 = true ∨ valuationOf q 959 = true := by
  have hs : count959 q = (countLit q [-54]) + (countLit q [-57]) := List.countP_append (p := literal q) (l₁ := [-54]) (l₂ := [-57])
  have hm := merge_right (literal (valuationOf q) (-57)) (literal (valuationOf q) (959)) (countLit q [-54]) (countLit q [-57]) (count959 q) 1 (meaningNeg57 q) (meaning959 q) hs
  change (! (valuationOf q 57)) = false ∨ valuationOf q 959 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1282 (q : Snake 81) (h : Conditions q) : valuation q 57 = true ∨ valuation q 959 = true := counterClause1282 (baseVal q)

theorem counterClause1283 (q : Nat → Bool) : valuationOf q 54 = true ∨ valuationOf q 959 = true := by
  have hs : count959 q = (countLit q [-54]) + (countLit q [-57]) := List.countP_append (p := literal q) (l₁ := [-54]) (l₂ := [-57])
  have hm := merge_left (literal (valuationOf q) (-54)) (literal (valuationOf q) (959)) (countLit q [-54]) (countLit q [-57]) (count959 q) 1 (meaningNeg54 q) (meaning959 q) hs
  change (! (valuationOf q 54)) = false ∨ valuationOf q 959 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1283 (q : Snake 81) (h : Conditions q) : valuation q 54 = true ∨ valuation q 959 = true := counterClause1283 (baseVal q)

theorem counterClause1284 (q : Nat → Bool) : valuationOf q 54 = true ∨ valuationOf q 57 = true ∨ valuationOf q 960 = true := by
  have hs : count959 q = (countLit q [-54]) + (countLit q [-57]) := List.countP_append (p := literal q) (l₁ := [-54]) (l₂ := [-57])
  have hm := merge_two (literal (valuationOf q) (-54)) (literal (valuationOf q) (-57)) (literal (valuationOf q) (960)) (countLit q [-54]) (countLit q [-57]) (count959 q) 1 1 (meaningNeg54 q) (meaningNeg57 q) (meaning960 q) hs
  change (! (valuationOf q 54)) = false ∨ (! (valuationOf q 57)) = false ∨ valuationOf q 960 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1284 (q : Snake 81) (h : Conditions q) : valuation q 54 = true ∨ valuation q 57 = true ∨ valuation q 960 = true := counterClause1284 (baseVal q)

theorem counterClause1285 (q : Nat → Bool) : valuationOf q 60 = true ∨ valuationOf q 961 = true := by
  have hs : count961 q = (countLit q [-59]) + (countLit q [-60]) := List.countP_append (p := literal q) (l₁ := [-59]) (l₂ := [-60])
  have hm := merge_right (literal (valuationOf q) (-60)) (literal (valuationOf q) (961)) (countLit q [-59]) (countLit q [-60]) (count961 q) 1 (meaningNeg60 q) (meaning961 q) hs
  change (! (valuationOf q 60)) = false ∨ valuationOf q 961 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1285 (q : Snake 81) (h : Conditions q) : valuation q 60 = true ∨ valuation q 961 = true := counterClause1285 (baseVal q)

theorem counterClause1286 (q : Nat → Bool) : valuationOf q 59 = true ∨ valuationOf q 961 = true := by
  have hs : count961 q = (countLit q [-59]) + (countLit q [-60]) := List.countP_append (p := literal q) (l₁ := [-59]) (l₂ := [-60])
  have hm := merge_left (literal (valuationOf q) (-59)) (literal (valuationOf q) (961)) (countLit q [-59]) (countLit q [-60]) (count961 q) 1 (meaningNeg59 q) (meaning961 q) hs
  change (! (valuationOf q 59)) = false ∨ valuationOf q 961 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1286 (q : Snake 81) (h : Conditions q) : valuation q 59 = true ∨ valuation q 961 = true := counterClause1286 (baseVal q)

theorem counterClause1287 (q : Nat → Bool) : valuationOf q 59 = true ∨ valuationOf q 60 = true ∨ valuationOf q 962 = true := by
  have hs : count961 q = (countLit q [-59]) + (countLit q [-60]) := List.countP_append (p := literal q) (l₁ := [-59]) (l₂ := [-60])
  have hm := merge_two (literal (valuationOf q) (-59)) (literal (valuationOf q) (-60)) (literal (valuationOf q) (962)) (countLit q [-59]) (countLit q [-60]) (count961 q) 1 1 (meaningNeg59 q) (meaningNeg60 q) (meaning962 q) hs
  change (! (valuationOf q 59)) = false ∨ (! (valuationOf q 60)) = false ∨ valuationOf q 962 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1287 (q : Snake 81) (h : Conditions q) : valuation q 59 = true ∨ valuation q 60 = true ∨ valuation q 962 = true := counterClause1287 (baseVal q)

theorem counterClause1288 (q : Nat → Bool) : valuationOf q 961 = false ∨ valuationOf q 963 = true := by
  have hs : count963 q = (countLit q [-54, -57]) + (countLit q [-59, -60]) := List.countP_append (p := literal q) (l₁ := [-54, -57]) (l₂ := [-59, -60])
  have hm := merge_right (literal (valuationOf q) (961)) (literal (valuationOf q) (963)) (countLit q [-54, -57]) (countLit q [-59, -60]) (count963 q) 1 (meaning961 q) (meaning963 q) hs
  change valuationOf q 961 = false ∨ valuationOf q 963 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1288 (q : Snake 81) (h : Conditions q) : valuation q 961 = false ∨ valuation q 963 = true := counterClause1288 (baseVal q)

theorem counterClause1289 (q : Nat → Bool) : valuationOf q 962 = false ∨ valuationOf q 964 = true := by
  have hs : count963 q = (countLit q [-54, -57]) + (countLit q [-59, -60]) := List.countP_append (p := literal q) (l₁ := [-54, -57]) (l₂ := [-59, -60])
  have hm := merge_right (literal (valuationOf q) (962)) (literal (valuationOf q) (964)) (countLit q [-54, -57]) (countLit q [-59, -60]) (count963 q) 2 (meaning962 q) (meaning964 q) hs
  change valuationOf q 962 = false ∨ valuationOf q 964 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1289 (q : Snake 81) (h : Conditions q) : valuation q 962 = false ∨ valuation q 964 = true := counterClause1289 (baseVal q)

theorem counterClause1290 (q : Nat → Bool) : valuationOf q 959 = false ∨ valuationOf q 963 = true := by
  have hs : count963 q = (countLit q [-54, -57]) + (countLit q [-59, -60]) := List.countP_append (p := literal q) (l₁ := [-54, -57]) (l₂ := [-59, -60])
  have hm := merge_left (literal (valuationOf q) (959)) (literal (valuationOf q) (963)) (countLit q [-54, -57]) (countLit q [-59, -60]) (count963 q) 1 (meaning959 q) (meaning963 q) hs
  change valuationOf q 959 = false ∨ valuationOf q 963 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1290 (q : Snake 81) (h : Conditions q) : valuation q 959 = false ∨ valuation q 963 = true := counterClause1290 (baseVal q)

theorem counterClause1291 (q : Nat → Bool) : valuationOf q 959 = false ∨ valuationOf q 961 = false ∨ valuationOf q 964 = true := by
  have hs : count963 q = (countLit q [-54, -57]) + (countLit q [-59, -60]) := List.countP_append (p := literal q) (l₁ := [-54, -57]) (l₂ := [-59, -60])
  have hm := merge_two (literal (valuationOf q) (959)) (literal (valuationOf q) (961)) (literal (valuationOf q) (964)) (countLit q [-54, -57]) (countLit q [-59, -60]) (count963 q) 1 1 (meaning959 q) (meaning961 q) (meaning964 q) hs
  change valuationOf q 959 = false ∨ valuationOf q 961 = false ∨ valuationOf q 964 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1291 (q : Snake 81) (h : Conditions q) : valuation q 959 = false ∨ valuation q 961 = false ∨ valuation q 964 = true := counterClause1291 (baseVal q)

theorem counterClause1292 (q : Nat → Bool) : valuationOf q 959 = false ∨ valuationOf q 962 = false ∨ valuationOf q 965 = true := by
  have hs : count963 q = (countLit q [-54, -57]) + (countLit q [-59, -60]) := List.countP_append (p := literal q) (l₁ := [-54, -57]) (l₂ := [-59, -60])
  have hm := merge_two (literal (valuationOf q) (959)) (literal (valuationOf q) (962)) (literal (valuationOf q) (965)) (countLit q [-54, -57]) (countLit q [-59, -60]) (count963 q) 1 2 (meaning959 q) (meaning962 q) (meaning965 q) hs
  change valuationOf q 959 = false ∨ valuationOf q 962 = false ∨ valuationOf q 965 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1292 (q : Snake 81) (h : Conditions q) : valuation q 959 = false ∨ valuation q 962 = false ∨ valuation q 965 = true := counterClause1292 (baseVal q)

theorem counterClause1293 (q : Nat → Bool) : valuationOf q 960 = false ∨ valuationOf q 964 = true := by
  have hs : count963 q = (countLit q [-54, -57]) + (countLit q [-59, -60]) := List.countP_append (p := literal q) (l₁ := [-54, -57]) (l₂ := [-59, -60])
  have hm := merge_left (literal (valuationOf q) (960)) (literal (valuationOf q) (964)) (countLit q [-54, -57]) (countLit q [-59, -60]) (count963 q) 2 (meaning960 q) (meaning964 q) hs
  change valuationOf q 960 = false ∨ valuationOf q 964 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1293 (q : Snake 81) (h : Conditions q) : valuation q 960 = false ∨ valuation q 964 = true := counterClause1293 (baseVal q)

theorem counterClause1294 (q : Nat → Bool) : valuationOf q 960 = false ∨ valuationOf q 961 = false ∨ valuationOf q 965 = true := by
  have hs : count963 q = (countLit q [-54, -57]) + (countLit q [-59, -60]) := List.countP_append (p := literal q) (l₁ := [-54, -57]) (l₂ := [-59, -60])
  have hm := merge_two (literal (valuationOf q) (960)) (literal (valuationOf q) (961)) (literal (valuationOf q) (965)) (countLit q [-54, -57]) (countLit q [-59, -60]) (count963 q) 2 1 (meaning960 q) (meaning961 q) (meaning965 q) hs
  change valuationOf q 960 = false ∨ valuationOf q 961 = false ∨ valuationOf q 965 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1294 (q : Snake 81) (h : Conditions q) : valuation q 960 = false ∨ valuation q 961 = false ∨ valuation q 965 = true := counterClause1294 (baseVal q)

theorem counterClause1295 (q : Nat → Bool) : valuationOf q 963 = false ∨ valuationOf q 967 = true := by
  have hs : count967 q = (countLit q [-46, -47, -51, -53]) + (countLit q [-54, -57, -59, -60]) := List.countP_append (p := literal q) (l₁ := [-46, -47, -51, -53]) (l₂ := [-54, -57, -59, -60])
  have hm := merge_right (literal (valuationOf q) (963)) (literal (valuationOf q) (967)) (countLit q [-46, -47, -51, -53]) (countLit q [-54, -57, -59, -60]) (count967 q) 1 (meaning963 q) (meaning967 q) hs
  change valuationOf q 963 = false ∨ valuationOf q 967 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1295 (q : Snake 81) (h : Conditions q) : valuation q 963 = false ∨ valuation q 967 = true := counterClause1295 (baseVal q)

theorem counterClause1296 (q : Nat → Bool) : valuationOf q 964 = false ∨ valuationOf q 968 = true := by
  have hs : count967 q = (countLit q [-46, -47, -51, -53]) + (countLit q [-54, -57, -59, -60]) := List.countP_append (p := literal q) (l₁ := [-46, -47, -51, -53]) (l₂ := [-54, -57, -59, -60])
  have hm := merge_right (literal (valuationOf q) (964)) (literal (valuationOf q) (968)) (countLit q [-46, -47, -51, -53]) (countLit q [-54, -57, -59, -60]) (count967 q) 2 (meaning964 q) (meaning968 q) hs
  change valuationOf q 964 = false ∨ valuationOf q 968 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1296 (q : Snake 81) (h : Conditions q) : valuation q 964 = false ∨ valuation q 968 = true := counterClause1296 (baseVal q)

theorem counterClause1297 (q : Nat → Bool) : valuationOf q 965 = false ∨ valuationOf q 969 = true := by
  have hs : count967 q = (countLit q [-46, -47, -51, -53]) + (countLit q [-54, -57, -59, -60]) := List.countP_append (p := literal q) (l₁ := [-46, -47, -51, -53]) (l₂ := [-54, -57, -59, -60])
  have hm := merge_right (literal (valuationOf q) (965)) (literal (valuationOf q) (969)) (countLit q [-46, -47, -51, -53]) (countLit q [-54, -57, -59, -60]) (count967 q) 3 (meaning965 q) (meaning969 q) hs
  change valuationOf q 965 = false ∨ valuationOf q 969 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1297 (q : Snake 81) (h : Conditions q) : valuation q 965 = false ∨ valuation q 969 = true := counterClause1297 (baseVal q)

theorem counterClause1298 (q : Nat → Bool) : valuationOf q 955 = false ∨ valuationOf q 967 = true := by
  have hs : count967 q = (countLit q [-46, -47, -51, -53]) + (countLit q [-54, -57, -59, -60]) := List.countP_append (p := literal q) (l₁ := [-46, -47, -51, -53]) (l₂ := [-54, -57, -59, -60])
  have hm := merge_left (literal (valuationOf q) (955)) (literal (valuationOf q) (967)) (countLit q [-46, -47, -51, -53]) (countLit q [-54, -57, -59, -60]) (count967 q) 1 (meaning955 q) (meaning967 q) hs
  change valuationOf q 955 = false ∨ valuationOf q 967 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1298 (q : Snake 81) (h : Conditions q) : valuation q 955 = false ∨ valuation q 967 = true := counterClause1298 (baseVal q)

theorem counterClause1299 (q : Nat → Bool) : valuationOf q 955 = false ∨ valuationOf q 963 = false ∨ valuationOf q 968 = true := by
  have hs : count967 q = (countLit q [-46, -47, -51, -53]) + (countLit q [-54, -57, -59, -60]) := List.countP_append (p := literal q) (l₁ := [-46, -47, -51, -53]) (l₂ := [-54, -57, -59, -60])
  have hm := merge_two (literal (valuationOf q) (955)) (literal (valuationOf q) (963)) (literal (valuationOf q) (968)) (countLit q [-46, -47, -51, -53]) (countLit q [-54, -57, -59, -60]) (count967 q) 1 1 (meaning955 q) (meaning963 q) (meaning968 q) hs
  change valuationOf q 955 = false ∨ valuationOf q 963 = false ∨ valuationOf q 968 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1299 (q : Snake 81) (h : Conditions q) : valuation q 955 = false ∨ valuation q 963 = false ∨ valuation q 968 = true := counterClause1299 (baseVal q)

theorem counterClause1300 (q : Nat → Bool) : valuationOf q 955 = false ∨ valuationOf q 964 = false ∨ valuationOf q 969 = true := by
  have hs : count967 q = (countLit q [-46, -47, -51, -53]) + (countLit q [-54, -57, -59, -60]) := List.countP_append (p := literal q) (l₁ := [-46, -47, -51, -53]) (l₂ := [-54, -57, -59, -60])
  have hm := merge_two (literal (valuationOf q) (955)) (literal (valuationOf q) (964)) (literal (valuationOf q) (969)) (countLit q [-46, -47, -51, -53]) (countLit q [-54, -57, -59, -60]) (count967 q) 1 2 (meaning955 q) (meaning964 q) (meaning969 q) hs
  change valuationOf q 955 = false ∨ valuationOf q 964 = false ∨ valuationOf q 969 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1300 (q : Snake 81) (h : Conditions q) : valuation q 955 = false ∨ valuation q 964 = false ∨ valuation q 969 = true := counterClause1300 (baseVal q)

theorem counterClause1301 (q : Nat → Bool) : valuationOf q 955 = false ∨ valuationOf q 965 = false ∨ valuationOf q 970 = true := by
  have hs : count967 q = (countLit q [-46, -47, -51, -53]) + (countLit q [-54, -57, -59, -60]) := List.countP_append (p := literal q) (l₁ := [-46, -47, -51, -53]) (l₂ := [-54, -57, -59, -60])
  have hm := merge_two (literal (valuationOf q) (955)) (literal (valuationOf q) (965)) (literal (valuationOf q) (970)) (countLit q [-46, -47, -51, -53]) (countLit q [-54, -57, -59, -60]) (count967 q) 1 3 (meaning955 q) (meaning965 q) (meaning970 q) hs
  change valuationOf q 955 = false ∨ valuationOf q 965 = false ∨ valuationOf q 970 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1301 (q : Snake 81) (h : Conditions q) : valuation q 955 = false ∨ valuation q 965 = false ∨ valuation q 970 = true := counterClause1301 (baseVal q)

theorem counterClause1302 (q : Nat → Bool) : valuationOf q 956 = false ∨ valuationOf q 968 = true := by
  have hs : count967 q = (countLit q [-46, -47, -51, -53]) + (countLit q [-54, -57, -59, -60]) := List.countP_append (p := literal q) (l₁ := [-46, -47, -51, -53]) (l₂ := [-54, -57, -59, -60])
  have hm := merge_left (literal (valuationOf q) (956)) (literal (valuationOf q) (968)) (countLit q [-46, -47, -51, -53]) (countLit q [-54, -57, -59, -60]) (count967 q) 2 (meaning956 q) (meaning968 q) hs
  change valuationOf q 956 = false ∨ valuationOf q 968 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1302 (q : Snake 81) (h : Conditions q) : valuation q 956 = false ∨ valuation q 968 = true := counterClause1302 (baseVal q)

theorem counterClause1303 (q : Nat → Bool) : valuationOf q 956 = false ∨ valuationOf q 963 = false ∨ valuationOf q 969 = true := by
  have hs : count967 q = (countLit q [-46, -47, -51, -53]) + (countLit q [-54, -57, -59, -60]) := List.countP_append (p := literal q) (l₁ := [-46, -47, -51, -53]) (l₂ := [-54, -57, -59, -60])
  have hm := merge_two (literal (valuationOf q) (956)) (literal (valuationOf q) (963)) (literal (valuationOf q) (969)) (countLit q [-46, -47, -51, -53]) (countLit q [-54, -57, -59, -60]) (count967 q) 2 1 (meaning956 q) (meaning963 q) (meaning969 q) hs
  change valuationOf q 956 = false ∨ valuationOf q 963 = false ∨ valuationOf q 969 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1303 (q : Snake 81) (h : Conditions q) : valuation q 956 = false ∨ valuation q 963 = false ∨ valuation q 969 = true := counterClause1303 (baseVal q)

theorem counterClause1304 (q : Nat → Bool) : valuationOf q 956 = false ∨ valuationOf q 964 = false ∨ valuationOf q 970 = true := by
  have hs : count967 q = (countLit q [-46, -47, -51, -53]) + (countLit q [-54, -57, -59, -60]) := List.countP_append (p := literal q) (l₁ := [-46, -47, -51, -53]) (l₂ := [-54, -57, -59, -60])
  have hm := merge_two (literal (valuationOf q) (956)) (literal (valuationOf q) (964)) (literal (valuationOf q) (970)) (countLit q [-46, -47, -51, -53]) (countLit q [-54, -57, -59, -60]) (count967 q) 2 2 (meaning956 q) (meaning964 q) (meaning970 q) hs
  change valuationOf q 956 = false ∨ valuationOf q 964 = false ∨ valuationOf q 970 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1304 (q : Snake 81) (h : Conditions q) : valuation q 956 = false ∨ valuation q 964 = false ∨ valuation q 970 = true := counterClause1304 (baseVal q)

theorem counterClause1305 (q : Nat → Bool) : valuationOf q 956 = false ∨ valuationOf q 965 = false ∨ valuationOf q 971 = true := by
  have hs : count967 q = (countLit q [-46, -47, -51, -53]) + (countLit q [-54, -57, -59, -60]) := List.countP_append (p := literal q) (l₁ := [-46, -47, -51, -53]) (l₂ := [-54, -57, -59, -60])
  have hm := merge_two (literal (valuationOf q) (956)) (literal (valuationOf q) (965)) (literal (valuationOf q) (971)) (countLit q [-46, -47, -51, -53]) (countLit q [-54, -57, -59, -60]) (count967 q) 2 3 (meaning956 q) (meaning965 q) (meaning971 q) hs
  change valuationOf q 956 = false ∨ valuationOf q 965 = false ∨ valuationOf q 971 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1305 (q : Snake 81) (h : Conditions q) : valuation q 956 = false ∨ valuation q 965 = false ∨ valuation q 971 = true := counterClause1305 (baseVal q)

theorem counterClause1306 (q : Nat → Bool) : valuationOf q 957 = false ∨ valuationOf q 969 = true := by
  have hs : count967 q = (countLit q [-46, -47, -51, -53]) + (countLit q [-54, -57, -59, -60]) := List.countP_append (p := literal q) (l₁ := [-46, -47, -51, -53]) (l₂ := [-54, -57, -59, -60])
  have hm := merge_left (literal (valuationOf q) (957)) (literal (valuationOf q) (969)) (countLit q [-46, -47, -51, -53]) (countLit q [-54, -57, -59, -60]) (count967 q) 3 (meaning957 q) (meaning969 q) hs
  change valuationOf q 957 = false ∨ valuationOf q 969 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1306 (q : Snake 81) (h : Conditions q) : valuation q 957 = false ∨ valuation q 969 = true := counterClause1306 (baseVal q)

theorem counterClause1307 (q : Nat → Bool) : valuationOf q 957 = false ∨ valuationOf q 963 = false ∨ valuationOf q 970 = true := by
  have hs : count967 q = (countLit q [-46, -47, -51, -53]) + (countLit q [-54, -57, -59, -60]) := List.countP_append (p := literal q) (l₁ := [-46, -47, -51, -53]) (l₂ := [-54, -57, -59, -60])
  have hm := merge_two (literal (valuationOf q) (957)) (literal (valuationOf q) (963)) (literal (valuationOf q) (970)) (countLit q [-46, -47, -51, -53]) (countLit q [-54, -57, -59, -60]) (count967 q) 3 1 (meaning957 q) (meaning963 q) (meaning970 q) hs
  change valuationOf q 957 = false ∨ valuationOf q 963 = false ∨ valuationOf q 970 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1307 (q : Snake 81) (h : Conditions q) : valuation q 957 = false ∨ valuation q 963 = false ∨ valuation q 970 = true := counterClause1307 (baseVal q)

theorem counterClause1308 (q : Nat → Bool) : valuationOf q 957 = false ∨ valuationOf q 964 = false ∨ valuationOf q 971 = true := by
  have hs : count967 q = (countLit q [-46, -47, -51, -53]) + (countLit q [-54, -57, -59, -60]) := List.countP_append (p := literal q) (l₁ := [-46, -47, -51, -53]) (l₂ := [-54, -57, -59, -60])
  have hm := merge_two (literal (valuationOf q) (957)) (literal (valuationOf q) (964)) (literal (valuationOf q) (971)) (countLit q [-46, -47, -51, -53]) (countLit q [-54, -57, -59, -60]) (count967 q) 3 2 (meaning957 q) (meaning964 q) (meaning971 q) hs
  change valuationOf q 957 = false ∨ valuationOf q 964 = false ∨ valuationOf q 971 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1308 (q : Snake 81) (h : Conditions q) : valuation q 957 = false ∨ valuation q 964 = false ∨ valuation q 971 = true := counterClause1308 (baseVal q)

theorem counterClause1309 (q : Nat → Bool) : valuationOf q 957 = false ∨ valuationOf q 965 = false ∨ valuationOf q 972 = true := by
  have hs : count967 q = (countLit q [-46, -47, -51, -53]) + (countLit q [-54, -57, -59, -60]) := List.countP_append (p := literal q) (l₁ := [-46, -47, -51, -53]) (l₂ := [-54, -57, -59, -60])
  have hm := merge_two (literal (valuationOf q) (957)) (literal (valuationOf q) (965)) (literal (valuationOf q) (972)) (countLit q [-46, -47, -51, -53]) (countLit q [-54, -57, -59, -60]) (count967 q) 3 3 (meaning957 q) (meaning965 q) (meaning972 q) hs
  change valuationOf q 957 = false ∨ valuationOf q 965 = false ∨ valuationOf q 972 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1309 (q : Snake 81) (h : Conditions q) : valuation q 957 = false ∨ valuation q 965 = false ∨ valuation q 972 = true := counterClause1309 (baseVal q)

theorem counterClause1310 (q : Nat → Bool) : valuationOf q 958 = false ∨ valuationOf q 970 = true := by
  have hs : count967 q = (countLit q [-46, -47, -51, -53]) + (countLit q [-54, -57, -59, -60]) := List.countP_append (p := literal q) (l₁ := [-46, -47, -51, -53]) (l₂ := [-54, -57, -59, -60])
  have hm := merge_left (literal (valuationOf q) (958)) (literal (valuationOf q) (970)) (countLit q [-46, -47, -51, -53]) (countLit q [-54, -57, -59, -60]) (count967 q) 4 (meaning958 q) (meaning970 q) hs
  change valuationOf q 958 = false ∨ valuationOf q 970 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1310 (q : Snake 81) (h : Conditions q) : valuation q 958 = false ∨ valuation q 970 = true := counterClause1310 (baseVal q)

theorem counterClause1311 (q : Nat → Bool) : valuationOf q 943 = false ∨ valuationOf q 971 = false ∨ valuationOf q 980 = true := by
  have hs : count975 q = (countLit q [-32, -34, -35, -36, -38, -42, -43, -44]) + (countLit q [-46, -47, -51, -53, -54, -57, -59, -60]) := List.countP_append (p := literal q) (l₁ := [-32, -34, -35, -36, -38, -42, -43, -44]) (l₂ := [-46, -47, -51, -53, -54, -57, -59, -60])
  have hm := merge_two (literal (valuationOf q) (943)) (literal (valuationOf q) (971)) (literal (valuationOf q) (980)) (countLit q [-32, -34, -35, -36, -38, -42, -43, -44]) (countLit q [-46, -47, -51, -53, -54, -57, -59, -60]) (count975 q) 1 5 (meaning943 q) (meaning971 q) (meaning980 q) hs
  change valuationOf q 943 = false ∨ valuationOf q 971 = false ∨ valuationOf q 980 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1311 (q : Snake 81) (h : Conditions q) : valuation q 943 = false ∨ valuation q 971 = false ∨ valuation q 980 = true := counterClause1311 (baseVal q)

theorem counterClause1312 (q : Nat → Bool) : valuationOf q 944 = false ∨ valuationOf q 969 = false ∨ valuationOf q 979 = true := by
  have hs : count975 q = (countLit q [-32, -34, -35, -36, -38, -42, -43, -44]) + (countLit q [-46, -47, -51, -53, -54, -57, -59, -60]) := List.countP_append (p := literal q) (l₁ := [-32, -34, -35, -36, -38, -42, -43, -44]) (l₂ := [-46, -47, -51, -53, -54, -57, -59, -60])
  have hm := merge_two (literal (valuationOf q) (944)) (literal (valuationOf q) (969)) (literal (valuationOf q) (979)) (countLit q [-32, -34, -35, -36, -38, -42, -43, -44]) (countLit q [-46, -47, -51, -53, -54, -57, -59, -60]) (count975 q) 2 3 (meaning944 q) (meaning969 q) (meaning979 q) hs
  change valuationOf q 944 = false ∨ valuationOf q 969 = false ∨ valuationOf q 979 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1312 (q : Snake 81) (h : Conditions q) : valuation q 944 = false ∨ valuation q 969 = false ∨ valuation q 979 = true := counterClause1312 (baseVal q)

theorem block40 (q : Snake 81) (h : Conditions q) : B112E121.Block40 (valuation q) :=
  ⟨clause1281 q h, clause1282 q h, clause1283 q h, clause1284 q h, clause1285 q h, clause1286 q h, clause1287 q h, clause1288 q h, clause1289 q h, clause1290 q h, clause1291 q h, clause1292 q h, clause1293 q h, clause1294 q h, clause1295 q h, clause1296 q h, clause1297 q h, clause1298 q h, clause1299 q h, clause1300 q h, clause1301 q h, clause1302 q h, clause1303 q h, clause1304 q h, clause1305 q h, clause1306 q h, clause1307 q h, clause1308 q h, clause1309 q h, clause1310 q h, clause1311 q h, clause1312 q h⟩

end
end Snake9.Regrowth.E112121
