import E112174Semantics
import B112E174Inputs
namespace Snake9.Regrowth.E112174
noncomputable section
local instance blockDec29 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause929 (q : Nat → Bool) : valuationOf q 68 = true ∨ valuationOf q 1337 = true := by
  have hs : count1337 q = (countLit q [-65]) + (countLit q [-68]) := List.countP_append (p := literal q) (l₁ := [-65]) (l₂ := [-68])
  have hm := merge_right (literal (valuationOf q) (-68)) (literal (valuationOf q) (1337)) (countLit q [-65]) (countLit q [-68]) (count1337 q) 1 (meaningNeg68 q) (meaning1337 q) hs
  change (! (valuationOf q 68)) = false ∨ valuationOf q 1337 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause929 (q : Snake 81) (h : Conditions q) : valuation q 68 = true ∨ valuation q 1337 = true := counterClause929 (baseVal q)

theorem counterClause930 (q : Nat → Bool) : valuationOf q 65 = true ∨ valuationOf q 1337 = true := by
  have hs : count1337 q = (countLit q [-65]) + (countLit q [-68]) := List.countP_append (p := literal q) (l₁ := [-65]) (l₂ := [-68])
  have hm := merge_left (literal (valuationOf q) (-65)) (literal (valuationOf q) (1337)) (countLit q [-65]) (countLit q [-68]) (count1337 q) 1 (meaningNeg65 q) (meaning1337 q) hs
  change (! (valuationOf q 65)) = false ∨ valuationOf q 1337 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause930 (q : Snake 81) (h : Conditions q) : valuation q 65 = true ∨ valuation q 1337 = true := counterClause930 (baseVal q)

theorem counterClause931 (q : Nat → Bool) : valuationOf q 1337 = false ∨ valuationOf q 1339 = true := by
  have hs : count1339 q = (countLit q [-63]) + (countLit q [-65, -68]) := List.countP_append (p := literal q) (l₁ := [-63]) (l₂ := [-65, -68])
  have hm := merge_right (literal (valuationOf q) (1337)) (literal (valuationOf q) (1339)) (countLit q [-63]) (countLit q [-65, -68]) (count1339 q) 1 (meaning1337 q) (meaning1339 q) hs
  change valuationOf q 1337 = false ∨ valuationOf q 1339 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause931 (q : Snake 81) (h : Conditions q) : valuation q 1337 = false ∨ valuation q 1339 = true := counterClause931 (baseVal q)

theorem counterClause932 (q : Nat → Bool) : valuationOf q 63 = true ∨ valuationOf q 1339 = true := by
  have hs : count1339 q = (countLit q [-63]) + (countLit q [-65, -68]) := List.countP_append (p := literal q) (l₁ := [-63]) (l₂ := [-65, -68])
  have hm := merge_left (literal (valuationOf q) (-63)) (literal (valuationOf q) (1339)) (countLit q [-63]) (countLit q [-65, -68]) (count1339 q) 1 (meaningNeg63 q) (meaning1339 q) hs
  change (! (valuationOf q 63)) = false ∨ valuationOf q 1339 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause932 (q : Snake 81) (h : Conditions q) : valuation q 63 = true ∨ valuation q 1339 = true := counterClause932 (baseVal q)

theorem counterClause933 (q : Nat → Bool) : valuationOf q 63 = true ∨ valuationOf q 1337 = false ∨ valuationOf q 1340 = true := by
  have hs : count1339 q = (countLit q [-63]) + (countLit q [-65, -68]) := List.countP_append (p := literal q) (l₁ := [-63]) (l₂ := [-65, -68])
  have hm := merge_two (literal (valuationOf q) (-63)) (literal (valuationOf q) (1337)) (literal (valuationOf q) (1340)) (countLit q [-63]) (countLit q [-65, -68]) (count1339 q) 1 1 (meaningNeg63 q) (meaning1337 q) (meaning1340 q) hs
  change (! (valuationOf q 63)) = false ∨ valuationOf q 1337 = false ∨ valuationOf q 1340 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause933 (q : Snake 81) (h : Conditions q) : valuation q 63 = true ∨ valuation q 1337 = false ∨ valuation q 1340 = true := counterClause933 (baseVal q)

theorem counterClause934 (q : Nat → Bool) : valuationOf q 76 = true ∨ valuationOf q 1344 = true := by
  have hs : count1344 q = (countLit q [-72]) + (countLit q [-76]) := List.countP_append (p := literal q) (l₁ := [-72]) (l₂ := [-76])
  have hm := merge_right (literal (valuationOf q) (-76)) (literal (valuationOf q) (1344)) (countLit q [-72]) (countLit q [-76]) (count1344 q) 1 (meaningNeg76 q) (meaning1344 q) hs
  change (! (valuationOf q 76)) = false ∨ valuationOf q 1344 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause934 (q : Snake 81) (h : Conditions q) : valuation q 76 = true ∨ valuation q 1344 = true := counterClause934 (baseVal q)

theorem counterClause935 (q : Nat → Bool) : valuationOf q 1344 = false ∨ valuationOf q 1346 = true := by
  have hs : count1346 q = (countLit q [-70, -71]) + (countLit q [-72, -76]) := List.countP_append (p := literal q) (l₁ := [-70, -71]) (l₂ := [-72, -76])
  have hm := merge_right (literal (valuationOf q) (1344)) (literal (valuationOf q) (1346)) (countLit q [-70, -71]) (countLit q [-72, -76]) (count1346 q) 1 (meaning1344 q) (meaning1346 q) hs
  change valuationOf q 1344 = false ∨ valuationOf q 1346 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause935 (q : Snake 81) (h : Conditions q) : valuation q 1344 = false ∨ valuation q 1346 = true := counterClause935 (baseVal q)

theorem counterClause936 (q : Nat → Bool) : valuationOf q 1346 = false ∨ valuationOf q 1350 = true := by
  have hs : count1350 q = (countLit q [-63, -65, -68]) + (countLit q [-70, -71, -72, -76]) := List.countP_append (p := literal q) (l₁ := [-63, -65, -68]) (l₂ := [-70, -71, -72, -76])
  have hm := merge_right (literal (valuationOf q) (1346)) (literal (valuationOf q) (1350)) (countLit q [-63, -65, -68]) (countLit q [-70, -71, -72, -76]) (count1350 q) 1 (meaning1346 q) (meaning1350 q) hs
  change valuationOf q 1346 = false ∨ valuationOf q 1350 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause936 (q : Snake 81) (h : Conditions q) : valuation q 1346 = false ∨ valuation q 1350 = true := counterClause936 (baseVal q)

theorem counterClause937 (q : Nat → Bool) : valuationOf q 1339 = false ∨ valuationOf q 1350 = true := by
  have hs : count1350 q = (countLit q [-63, -65, -68]) + (countLit q [-70, -71, -72, -76]) := List.countP_append (p := literal q) (l₁ := [-63, -65, -68]) (l₂ := [-70, -71, -72, -76])
  have hm := merge_left (literal (valuationOf q) (1339)) (literal (valuationOf q) (1350)) (countLit q [-63, -65, -68]) (countLit q [-70, -71, -72, -76]) (count1350 q) 1 (meaning1339 q) (meaning1350 q) hs
  change valuationOf q 1339 = false ∨ valuationOf q 1350 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause937 (q : Snake 81) (h : Conditions q) : valuation q 1339 = false ∨ valuation q 1350 = true := counterClause937 (baseVal q)

theorem counterClause938 (q : Nat → Bool) : valuationOf q 1339 = false ∨ valuationOf q 1346 = false ∨ valuationOf q 1351 = true := by
  have hs : count1350 q = (countLit q [-63, -65, -68]) + (countLit q [-70, -71, -72, -76]) := List.countP_append (p := literal q) (l₁ := [-63, -65, -68]) (l₂ := [-70, -71, -72, -76])
  have hm := merge_two (literal (valuationOf q) (1339)) (literal (valuationOf q) (1346)) (literal (valuationOf q) (1351)) (countLit q [-63, -65, -68]) (countLit q [-70, -71, -72, -76]) (count1350 q) 1 1 (meaning1339 q) (meaning1346 q) (meaning1351 q) hs
  change valuationOf q 1339 = false ∨ valuationOf q 1346 = false ∨ valuationOf q 1351 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause938 (q : Snake 81) (h : Conditions q) : valuation q 1339 = false ∨ valuation q 1346 = false ∨ valuation q 1351 = true := counterClause938 (baseVal q)

theorem counterClause939 (q : Nat → Bool) : valuationOf q 1340 = false ∨ valuationOf q 1351 = true := by
  have hs : count1350 q = (countLit q [-63, -65, -68]) + (countLit q [-70, -71, -72, -76]) := List.countP_append (p := literal q) (l₁ := [-63, -65, -68]) (l₂ := [-70, -71, -72, -76])
  have hm := merge_left (literal (valuationOf q) (1340)) (literal (valuationOf q) (1351)) (countLit q [-63, -65, -68]) (countLit q [-70, -71, -72, -76]) (count1350 q) 2 (meaning1340 q) (meaning1351 q) hs
  change valuationOf q 1340 = false ∨ valuationOf q 1351 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause939 (q : Snake 81) (h : Conditions q) : valuation q 1340 = false ∨ valuation q 1351 = true := counterClause939 (baseVal q)

theorem counterClause940 (q : Nat → Bool) : valuationOf q 1350 = false ∨ valuationOf q 1357 = true := by
  have hs : count1357 q = (countLit q [-52, -54, -55, -57, -60, -62]) + (countLit q [-63, -65, -68, -70, -71, -72, -76]) := List.countP_append (p := literal q) (l₁ := [-52, -54, -55, -57, -60, -62]) (l₂ := [-63, -65, -68, -70, -71, -72, -76])
  have hm := merge_right (literal (valuationOf q) (1350)) (literal (valuationOf q) (1357)) (countLit q [-52, -54, -55, -57, -60, -62]) (countLit q [-63, -65, -68, -70, -71, -72, -76]) (count1357 q) 1 (meaning1350 q) (meaning1357 q) hs
  change valuationOf q 1350 = false ∨ valuationOf q 1357 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause940 (q : Snake 81) (h : Conditions q) : valuation q 1350 = false ∨ valuation q 1357 = true := counterClause940 (baseVal q)

theorem counterClause941 (q : Nat → Bool) : valuationOf q 1351 = false ∨ valuationOf q 1358 = true := by
  have hs : count1357 q = (countLit q [-52, -54, -55, -57, -60, -62]) + (countLit q [-63, -65, -68, -70, -71, -72, -76]) := List.countP_append (p := literal q) (l₁ := [-52, -54, -55, -57, -60, -62]) (l₂ := [-63, -65, -68, -70, -71, -72, -76])
  have hm := merge_right (literal (valuationOf q) (1351)) (literal (valuationOf q) (1358)) (countLit q [-52, -54, -55, -57, -60, -62]) (countLit q [-63, -65, -68, -70, -71, -72, -76]) (count1357 q) 2 (meaning1351 q) (meaning1358 q) hs
  change valuationOf q 1351 = false ∨ valuationOf q 1358 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause941 (q : Snake 81) (h : Conditions q) : valuation q 1351 = false ∨ valuation q 1358 = true := counterClause941 (baseVal q)

theorem counterClause942 (q : Nat → Bool) : valuationOf q 1331 = false ∨ valuationOf q 1357 = true := by
  have hs : count1357 q = (countLit q [-52, -54, -55, -57, -60, -62]) + (countLit q [-63, -65, -68, -70, -71, -72, -76]) := List.countP_append (p := literal q) (l₁ := [-52, -54, -55, -57, -60, -62]) (l₂ := [-63, -65, -68, -70, -71, -72, -76])
  have hm := merge_left (literal (valuationOf q) (1331)) (literal (valuationOf q) (1357)) (countLit q [-52, -54, -55, -57, -60, -62]) (countLit q [-63, -65, -68, -70, -71, -72, -76]) (count1357 q) 1 (meaning1331 q) (meaning1357 q) hs
  change valuationOf q 1331 = false ∨ valuationOf q 1357 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause942 (q : Snake 81) (h : Conditions q) : valuation q 1331 = false ∨ valuation q 1357 = true := counterClause942 (baseVal q)

theorem counterClause943 (q : Nat → Bool) : valuationOf q 1331 = false ∨ valuationOf q 1350 = false ∨ valuationOf q 1358 = true := by
  have hs : count1357 q = (countLit q [-52, -54, -55, -57, -60, -62]) + (countLit q [-63, -65, -68, -70, -71, -72, -76]) := List.countP_append (p := literal q) (l₁ := [-52, -54, -55, -57, -60, -62]) (l₂ := [-63, -65, -68, -70, -71, -72, -76])
  have hm := merge_two (literal (valuationOf q) (1331)) (literal (valuationOf q) (1350)) (literal (valuationOf q) (1358)) (countLit q [-52, -54, -55, -57, -60, -62]) (countLit q [-63, -65, -68, -70, -71, -72, -76]) (count1357 q) 1 1 (meaning1331 q) (meaning1350 q) (meaning1358 q) hs
  change valuationOf q 1331 = false ∨ valuationOf q 1350 = false ∨ valuationOf q 1358 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause943 (q : Snake 81) (h : Conditions q) : valuation q 1331 = false ∨ valuation q 1350 = false ∨ valuation q 1358 = true := counterClause943 (baseVal q)

theorem counterClause944 (q : Nat → Bool) : valuationOf q 1331 = false ∨ valuationOf q 1351 = false ∨ valuationOf q 1359 = true := by
  have hs : count1357 q = (countLit q [-52, -54, -55, -57, -60, -62]) + (countLit q [-63, -65, -68, -70, -71, -72, -76]) := List.countP_append (p := literal q) (l₁ := [-52, -54, -55, -57, -60, -62]) (l₂ := [-63, -65, -68, -70, -71, -72, -76])
  have hm := merge_two (literal (valuationOf q) (1331)) (literal (valuationOf q) (1351)) (literal (valuationOf q) (1359)) (countLit q [-52, -54, -55, -57, -60, -62]) (countLit q [-63, -65, -68, -70, -71, -72, -76]) (count1357 q) 1 2 (meaning1331 q) (meaning1351 q) (meaning1359 q) hs
  change valuationOf q 1331 = false ∨ valuationOf q 1351 = false ∨ valuationOf q 1359 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause944 (q : Snake 81) (h : Conditions q) : valuation q 1331 = false ∨ valuation q 1351 = false ∨ valuation q 1359 = true := counterClause944 (baseVal q)

theorem counterClause945 (q : Nat → Bool) : valuationOf q 1332 = false ∨ valuationOf q 1358 = true := by
  have hs : count1357 q = (countLit q [-52, -54, -55, -57, -60, -62]) + (countLit q [-63, -65, -68, -70, -71, -72, -76]) := List.countP_append (p := literal q) (l₁ := [-52, -54, -55, -57, -60, -62]) (l₂ := [-63, -65, -68, -70, -71, -72, -76])
  have hm := merge_left (literal (valuationOf q) (1332)) (literal (valuationOf q) (1358)) (countLit q [-52, -54, -55, -57, -60, -62]) (countLit q [-63, -65, -68, -70, -71, -72, -76]) (count1357 q) 2 (meaning1332 q) (meaning1358 q) hs
  change valuationOf q 1332 = false ∨ valuationOf q 1358 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause945 (q : Snake 81) (h : Conditions q) : valuation q 1332 = false ∨ valuation q 1358 = true := counterClause945 (baseVal q)

theorem counterClause946 (q : Nat → Bool) : valuationOf q 1332 = false ∨ valuationOf q 1350 = false ∨ valuationOf q 1359 = true := by
  have hs : count1357 q = (countLit q [-52, -54, -55, -57, -60, -62]) + (countLit q [-63, -65, -68, -70, -71, -72, -76]) := List.countP_append (p := literal q) (l₁ := [-52, -54, -55, -57, -60, -62]) (l₂ := [-63, -65, -68, -70, -71, -72, -76])
  have hm := merge_two (literal (valuationOf q) (1332)) (literal (valuationOf q) (1350)) (literal (valuationOf q) (1359)) (countLit q [-52, -54, -55, -57, -60, -62]) (countLit q [-63, -65, -68, -70, -71, -72, -76]) (count1357 q) 2 1 (meaning1332 q) (meaning1350 q) (meaning1359 q) hs
  change valuationOf q 1332 = false ∨ valuationOf q 1350 = false ∨ valuationOf q 1359 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause946 (q : Snake 81) (h : Conditions q) : valuation q 1332 = false ∨ valuation q 1350 = false ∨ valuation q 1359 = true := counterClause946 (baseVal q)

theorem counterClause947 (q : Nat → Bool) : valuationOf q 1332 = false ∨ valuationOf q 1351 = false ∨ valuationOf q 1360 = true := by
  have hs : count1357 q = (countLit q [-52, -54, -55, -57, -60, -62]) + (countLit q [-63, -65, -68, -70, -71, -72, -76]) := List.countP_append (p := literal q) (l₁ := [-52, -54, -55, -57, -60, -62]) (l₂ := [-63, -65, -68, -70, -71, -72, -76])
  have hm := merge_two (literal (valuationOf q) (1332)) (literal (valuationOf q) (1351)) (literal (valuationOf q) (1360)) (countLit q [-52, -54, -55, -57, -60, -62]) (countLit q [-63, -65, -68, -70, -71, -72, -76]) (count1357 q) 2 2 (meaning1332 q) (meaning1351 q) (meaning1360 q) hs
  change valuationOf q 1332 = false ∨ valuationOf q 1351 = false ∨ valuationOf q 1360 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause947 (q : Snake 81) (h : Conditions q) : valuation q 1332 = false ∨ valuation q 1351 = false ∨ valuation q 1360 = true := counterClause947 (baseVal q)

theorem counterClause948 (q : Nat → Bool) : valuationOf q 1333 = false ∨ valuationOf q 1359 = true := by
  have hs : count1357 q = (countLit q [-52, -54, -55, -57, -60, -62]) + (countLit q [-63, -65, -68, -70, -71, -72, -76]) := List.countP_append (p := literal q) (l₁ := [-52, -54, -55, -57, -60, -62]) (l₂ := [-63, -65, -68, -70, -71, -72, -76])
  have hm := merge_left (literal (valuationOf q) (1333)) (literal (valuationOf q) (1359)) (countLit q [-52, -54, -55, -57, -60, -62]) (countLit q [-63, -65, -68, -70, -71, -72, -76]) (count1357 q) 3 (meaning1333 q) (meaning1359 q) hs
  change valuationOf q 1333 = false ∨ valuationOf q 1359 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause948 (q : Snake 81) (h : Conditions q) : valuation q 1333 = false ∨ valuation q 1359 = true := counterClause948 (baseVal q)

theorem counterClause949 (q : Nat → Bool) : valuationOf q 1333 = false ∨ valuationOf q 1350 = false ∨ valuationOf q 1360 = true := by
  have hs : count1357 q = (countLit q [-52, -54, -55, -57, -60, -62]) + (countLit q [-63, -65, -68, -70, -71, -72, -76]) := List.countP_append (p := literal q) (l₁ := [-52, -54, -55, -57, -60, -62]) (l₂ := [-63, -65, -68, -70, -71, -72, -76])
  have hm := merge_two (literal (valuationOf q) (1333)) (literal (valuationOf q) (1350)) (literal (valuationOf q) (1360)) (countLit q [-52, -54, -55, -57, -60, -62]) (countLit q [-63, -65, -68, -70, -71, -72, -76]) (count1357 q) 3 1 (meaning1333 q) (meaning1350 q) (meaning1360 q) hs
  change valuationOf q 1333 = false ∨ valuationOf q 1350 = false ∨ valuationOf q 1360 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause949 (q : Snake 81) (h : Conditions q) : valuation q 1333 = false ∨ valuation q 1350 = false ∨ valuation q 1360 = true := counterClause949 (baseVal q)

theorem counterClause950 (q : Nat → Bool) : valuationOf q 1333 = false ∨ valuationOf q 1351 = false ∨ valuationOf q 1361 = true := by
  have hs : count1357 q = (countLit q [-52, -54, -55, -57, -60, -62]) + (countLit q [-63, -65, -68, -70, -71, -72, -76]) := List.countP_append (p := literal q) (l₁ := [-52, -54, -55, -57, -60, -62]) (l₂ := [-63, -65, -68, -70, -71, -72, -76])
  have hm := merge_two (literal (valuationOf q) (1333)) (literal (valuationOf q) (1351)) (literal (valuationOf q) (1361)) (countLit q [-52, -54, -55, -57, -60, -62]) (countLit q [-63, -65, -68, -70, -71, -72, -76]) (count1357 q) 3 2 (meaning1333 q) (meaning1351 q) (meaning1361 q) hs
  change valuationOf q 1333 = false ∨ valuationOf q 1351 = false ∨ valuationOf q 1361 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause950 (q : Snake 81) (h : Conditions q) : valuation q 1333 = false ∨ valuation q 1351 = false ∨ valuation q 1361 = true := counterClause950 (baseVal q)

theorem counterClause951 (q : Nat → Bool) : valuationOf q 1334 = false ∨ valuationOf q 1360 = true := by
  have hs : count1357 q = (countLit q [-52, -54, -55, -57, -60, -62]) + (countLit q [-63, -65, -68, -70, -71, -72, -76]) := List.countP_append (p := literal q) (l₁ := [-52, -54, -55, -57, -60, -62]) (l₂ := [-63, -65, -68, -70, -71, -72, -76])
  have hm := merge_left (literal (valuationOf q) (1334)) (literal (valuationOf q) (1360)) (countLit q [-52, -54, -55, -57, -60, -62]) (countLit q [-63, -65, -68, -70, -71, -72, -76]) (count1357 q) 4 (meaning1334 q) (meaning1360 q) hs
  change valuationOf q 1334 = false ∨ valuationOf q 1360 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause951 (q : Snake 81) (h : Conditions q) : valuation q 1334 = false ∨ valuation q 1360 = true := counterClause951 (baseVal q)

theorem counterClause952 (q : Nat → Bool) : valuationOf q 1334 = false ∨ valuationOf q 1350 = false ∨ valuationOf q 1361 = true := by
  have hs : count1357 q = (countLit q [-52, -54, -55, -57, -60, -62]) + (countLit q [-63, -65, -68, -70, -71, -72, -76]) := List.countP_append (p := literal q) (l₁ := [-52, -54, -55, -57, -60, -62]) (l₂ := [-63, -65, -68, -70, -71, -72, -76])
  have hm := merge_two (literal (valuationOf q) (1334)) (literal (valuationOf q) (1350)) (literal (valuationOf q) (1361)) (countLit q [-52, -54, -55, -57, -60, -62]) (countLit q [-63, -65, -68, -70, -71, -72, -76]) (count1357 q) 4 1 (meaning1334 q) (meaning1350 q) (meaning1361 q) hs
  change valuationOf q 1334 = false ∨ valuationOf q 1350 = false ∨ valuationOf q 1361 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause952 (q : Snake 81) (h : Conditions q) : valuation q 1334 = false ∨ valuation q 1350 = false ∨ valuation q 1361 = true := counterClause952 (baseVal q)

theorem counterClause953 (q : Nat → Bool) : valuationOf q 1334 = false ∨ valuationOf q 1351 = false ∨ valuationOf q 1362 = true := by
  have hs : count1357 q = (countLit q [-52, -54, -55, -57, -60, -62]) + (countLit q [-63, -65, -68, -70, -71, -72, -76]) := List.countP_append (p := literal q) (l₁ := [-52, -54, -55, -57, -60, -62]) (l₂ := [-63, -65, -68, -70, -71, -72, -76])
  have hm := merge_two (literal (valuationOf q) (1334)) (literal (valuationOf q) (1351)) (literal (valuationOf q) (1362)) (countLit q [-52, -54, -55, -57, -60, -62]) (countLit q [-63, -65, -68, -70, -71, -72, -76]) (count1357 q) 4 2 (meaning1334 q) (meaning1351 q) (meaning1362 q) hs
  change valuationOf q 1334 = false ∨ valuationOf q 1351 = false ∨ valuationOf q 1362 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause953 (q : Snake 81) (h : Conditions q) : valuation q 1334 = false ∨ valuation q 1351 = false ∨ valuation q 1362 = true := counterClause953 (baseVal q)

theorem counterClause954 (q : Nat → Bool) : valuationOf q 1335 = false ∨ valuationOf q 1361 = true := by
  have hs : count1357 q = (countLit q [-52, -54, -55, -57, -60, -62]) + (countLit q [-63, -65, -68, -70, -71, -72, -76]) := List.countP_append (p := literal q) (l₁ := [-52, -54, -55, -57, -60, -62]) (l₂ := [-63, -65, -68, -70, -71, -72, -76])
  have hm := merge_left (literal (valuationOf q) (1335)) (literal (valuationOf q) (1361)) (countLit q [-52, -54, -55, -57, -60, -62]) (countLit q [-63, -65, -68, -70, -71, -72, -76]) (count1357 q) 5 (meaning1335 q) (meaning1361 q) hs
  change valuationOf q 1335 = false ∨ valuationOf q 1361 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause954 (q : Snake 81) (h : Conditions q) : valuation q 1335 = false ∨ valuation q 1361 = true := counterClause954 (baseVal q)

theorem counterClause955 (q : Nat → Bool) : valuationOf q 1335 = false ∨ valuationOf q 1350 = false ∨ valuationOf q 1362 = true := by
  have hs : count1357 q = (countLit q [-52, -54, -55, -57, -60, -62]) + (countLit q [-63, -65, -68, -70, -71, -72, -76]) := List.countP_append (p := literal q) (l₁ := [-52, -54, -55, -57, -60, -62]) (l₂ := [-63, -65, -68, -70, -71, -72, -76])
  have hm := merge_two (literal (valuationOf q) (1335)) (literal (valuationOf q) (1350)) (literal (valuationOf q) (1362)) (countLit q [-52, -54, -55, -57, -60, -62]) (countLit q [-63, -65, -68, -70, -71, -72, -76]) (count1357 q) 5 1 (meaning1335 q) (meaning1350 q) (meaning1362 q) hs
  change valuationOf q 1335 = false ∨ valuationOf q 1350 = false ∨ valuationOf q 1362 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause955 (q : Snake 81) (h : Conditions q) : valuation q 1335 = false ∨ valuation q 1350 = false ∨ valuation q 1362 = true := counterClause955 (baseVal q)

theorem counterClause956 (q : Nat → Bool) : valuationOf q 1336 = false ∨ valuationOf q 1362 = true := by
  have hs : count1357 q = (countLit q [-52, -54, -55, -57, -60, -62]) + (countLit q [-63, -65, -68, -70, -71, -72, -76]) := List.countP_append (p := literal q) (l₁ := [-52, -54, -55, -57, -60, -62]) (l₂ := [-63, -65, -68, -70, -71, -72, -76])
  have hm := merge_left (literal (valuationOf q) (1336)) (literal (valuationOf q) (1362)) (countLit q [-52, -54, -55, -57, -60, -62]) (countLit q [-63, -65, -68, -70, -71, -72, -76]) (count1357 q) 6 (meaning1336 q) (meaning1362 q) hs
  change valuationOf q 1336 = false ∨ valuationOf q 1362 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause956 (q : Snake 81) (h : Conditions q) : valuation q 1336 = false ∨ valuation q 1362 = true := counterClause956 (baseVal q)

theorem counterClause957 (q : Nat → Bool) : valuationOf q 80 = true ∨ valuationOf q 1370 = true := by
  have hs : count1370 q = (countLit q [-79]) + (countLit q [-80]) := List.countP_append (p := literal q) (l₁ := [-79]) (l₂ := [-80])
  have hm := merge_right (literal (valuationOf q) (-80)) (literal (valuationOf q) (1370)) (countLit q [-79]) (countLit q [-80]) (count1370 q) 1 (meaningNeg80 q) (meaning1370 q) hs
  change (! (valuationOf q 80)) = false ∨ valuationOf q 1370 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause957 (q : Snake 81) (h : Conditions q) : valuation q 80 = true ∨ valuation q 1370 = true := counterClause957 (baseVal q)

theorem counterClause958 (q : Nat → Bool) : valuationOf q 79 = true ∨ valuationOf q 1370 = true := by
  have hs : count1370 q = (countLit q [-79]) + (countLit q [-80]) := List.countP_append (p := literal q) (l₁ := [-79]) (l₂ := [-80])
  have hm := merge_left (literal (valuationOf q) (-79)) (literal (valuationOf q) (1370)) (countLit q [-79]) (countLit q [-80]) (count1370 q) 1 (meaningNeg79 q) (meaning1370 q) hs
  change (! (valuationOf q 79)) = false ∨ valuationOf q 1370 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause958 (q : Snake 81) (h : Conditions q) : valuation q 79 = true ∨ valuation q 1370 = true := counterClause958 (baseVal q)

theorem counterClause959 (q : Nat → Bool) : valuationOf q 79 = true ∨ valuationOf q 80 = true ∨ valuationOf q 1371 = true := by
  have hs : count1370 q = (countLit q [-79]) + (countLit q [-80]) := List.countP_append (p := literal q) (l₁ := [-79]) (l₂ := [-80])
  have hm := merge_two (literal (valuationOf q) (-79)) (literal (valuationOf q) (-80)) (literal (valuationOf q) (1371)) (countLit q [-79]) (countLit q [-80]) (count1370 q) 1 1 (meaningNeg79 q) (meaningNeg80 q) (meaning1371 q) hs
  change (! (valuationOf q 79)) = false ∨ (! (valuationOf q 80)) = false ∨ valuationOf q 1371 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause959 (q : Snake 81) (h : Conditions q) : valuation q 79 = true ∨ valuation q 80 = true ∨ valuation q 1371 = true := counterClause959 (baseVal q)

theorem counterClause960 (q : Nat → Bool) : valuationOf q 1370 = false ∨ valuationOf q 1372 = true := by
  have hs : count1372 q = (countLit q [-78]) + (countLit q [-79, -80]) := List.countP_append (p := literal q) (l₁ := [-78]) (l₂ := [-79, -80])
  have hm := merge_right (literal (valuationOf q) (1370)) (literal (valuationOf q) (1372)) (countLit q [-78]) (countLit q [-79, -80]) (count1372 q) 1 (meaning1370 q) (meaning1372 q) hs
  change valuationOf q 1370 = false ∨ valuationOf q 1372 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause960 (q : Snake 81) (h : Conditions q) : valuation q 1370 = false ∨ valuation q 1372 = true := counterClause960 (baseVal q)

theorem block29 (q : Snake 81) (h : Conditions q) : B112E174.Block29 (valuation q) :=
  ⟨clause929 q h, clause930 q h, clause931 q h, clause932 q h, clause933 q h, clause934 q h, clause935 q h, clause936 q h, clause937 q h, clause938 q h, clause939 q h, clause940 q h, clause941 q h, clause942 q h, clause943 q h, clause944 q h, clause945 q h, clause946 q h, clause947 q h, clause948 q h, clause949 q h, clause950 q h, clause951 q h, clause952 q h, clause953 q h, clause954 q h, clause955 q h, clause956 q h, clause957 q h, clause958 q h, clause959 q h, clause960 q h⟩

end
end Snake9.Regrowth.E112174
