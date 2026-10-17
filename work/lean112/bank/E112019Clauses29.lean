import E112019Semantics
import B112E019Inputs
namespace Snake9.Regrowth.E112019
noncomputable section
local instance blockDec29 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause929 (q : Nat → Bool) : valuationOf q 267 = false ∨ valuationOf q 269 = true := by
  have hs : count269 q = (countLit q [122, 123, 124, 125, 126, 127, 128]) + (countLit q [129, 130, 131, 132, 133, 134, 135, 136]) := List.countP_append (p := literal q) (l₁ := [122, 123, 124, 125, 126, 127, 128]) (l₂ := [129, 130, 131, 132, 133, 134, 135, 136])
  have hm := merge_right (literal (valuationOf q) (267)) (literal (valuationOf q) (269)) (countLit q [122, 123, 124, 125, 126, 127, 128]) (countLit q [129, 130, 131, 132, 133, 134, 135, 136]) (count269 q) 1 (meaning267 q) (meaning269 q) hs
  change valuationOf q 267 = false ∨ valuationOf q 269 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause929 (q : Snake 81) (h : Conditions q) : valuation q 267 = false ∨ valuation q 269 = true := counterClause929 (baseVal q)

theorem counterClause930 (q : Nat → Bool) : valuationOf q 253 = false ∨ valuationOf q 269 = true := by
  have hs : count269 q = (countLit q [122, 123, 124, 125, 126, 127, 128]) + (countLit q [129, 130, 131, 132, 133, 134, 135, 136]) := List.countP_append (p := literal q) (l₁ := [122, 123, 124, 125, 126, 127, 128]) (l₂ := [129, 130, 131, 132, 133, 134, 135, 136])
  have hm := merge_left (literal (valuationOf q) (253)) (literal (valuationOf q) (269)) (countLit q [122, 123, 124, 125, 126, 127, 128]) (countLit q [129, 130, 131, 132, 133, 134, 135, 136]) (count269 q) 1 (meaning253 q) (meaning269 q) hs
  change valuationOf q 253 = false ∨ valuationOf q 269 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause930 (q : Snake 81) (h : Conditions q) : valuation q 253 = false ∨ valuation q 269 = true := counterClause930 (baseVal q)

theorem counterClause931 (q : Nat → Bool) : valuationOf q 253 = false ∨ valuationOf q 267 = false ∨ valuationOf q 270 = true := by
  have hs : count269 q = (countLit q [122, 123, 124, 125, 126, 127, 128]) + (countLit q [129, 130, 131, 132, 133, 134, 135, 136]) := List.countP_append (p := literal q) (l₁ := [122, 123, 124, 125, 126, 127, 128]) (l₂ := [129, 130, 131, 132, 133, 134, 135, 136])
  have hm := merge_two (literal (valuationOf q) (253)) (literal (valuationOf q) (267)) (literal (valuationOf q) (270)) (countLit q [122, 123, 124, 125, 126, 127, 128]) (countLit q [129, 130, 131, 132, 133, 134, 135, 136]) (count269 q) 1 1 (meaning253 q) (meaning267 q) (meaning270 q) hs
  change valuationOf q 253 = false ∨ valuationOf q 267 = false ∨ valuationOf q 270 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause931 (q : Snake 81) (h : Conditions q) : valuation q 253 = false ∨ valuation q 267 = false ∨ valuation q 270 = true := counterClause931 (baseVal q)

theorem counterClause932 (q : Nat → Bool) : valuationOf q 254 = false ∨ valuationOf q 270 = true := by
  have hs : count269 q = (countLit q [122, 123, 124, 125, 126, 127, 128]) + (countLit q [129, 130, 131, 132, 133, 134, 135, 136]) := List.countP_append (p := literal q) (l₁ := [122, 123, 124, 125, 126, 127, 128]) (l₂ := [129, 130, 131, 132, 133, 134, 135, 136])
  have hm := merge_left (literal (valuationOf q) (254)) (literal (valuationOf q) (270)) (countLit q [122, 123, 124, 125, 126, 127, 128]) (countLit q [129, 130, 131, 132, 133, 134, 135, 136]) (count269 q) 2 (meaning254 q) (meaning270 q) hs
  change valuationOf q 254 = false ∨ valuationOf q 270 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause932 (q : Snake 81) (h : Conditions q) : valuation q 254 = false ∨ valuation q 270 = true := counterClause932 (baseVal q)

theorem counterClause933 (q : Nat → Bool) : valuationOf q 139 = false ∨ valuationOf q 271 = true := by
  have hs : count271 q = (countLit q [138]) + (countLit q [139]) := List.countP_append (p := literal q) (l₁ := [138]) (l₂ := [139])
  have hm := merge_right (literal (valuationOf q) (139)) (literal (valuationOf q) (271)) (countLit q [138]) (countLit q [139]) (count271 q) 1 (meaning139 q) (meaning271 q) hs
  change valuationOf q 139 = false ∨ valuationOf q 271 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause933 (q : Snake 81) (h : Conditions q) : valuation q 139 = false ∨ valuation q 271 = true := counterClause933 (baseVal q)

theorem counterClause934 (q : Nat → Bool) : valuationOf q 271 = false ∨ valuationOf q 273 = true := by
  have hs : count273 q = (countLit q [137]) + (countLit q [138, 139]) := List.countP_append (p := literal q) (l₁ := [137]) (l₂ := [138, 139])
  have hm := merge_right (literal (valuationOf q) (271)) (literal (valuationOf q) (273)) (countLit q [137]) (countLit q [138, 139]) (count273 q) 1 (meaning271 q) (meaning273 q) hs
  change valuationOf q 271 = false ∨ valuationOf q 273 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause934 (q : Snake 81) (h : Conditions q) : valuation q 271 = false ∨ valuation q 273 = true := counterClause934 (baseVal q)

theorem counterClause935 (q : Nat → Bool) : valuationOf q 137 = false ∨ valuationOf q 273 = true := by
  have hs : count273 q = (countLit q [137]) + (countLit q [138, 139]) := List.countP_append (p := literal q) (l₁ := [137]) (l₂ := [138, 139])
  have hm := merge_left (literal (valuationOf q) (137)) (literal (valuationOf q) (273)) (countLit q [137]) (countLit q [138, 139]) (count273 q) 1 (meaning137 q) (meaning273 q) hs
  change valuationOf q 137 = false ∨ valuationOf q 273 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause935 (q : Snake 81) (h : Conditions q) : valuation q 137 = false ∨ valuation q 273 = true := counterClause935 (baseVal q)

theorem counterClause936 (q : Nat → Bool) : valuationOf q 140 = false ∨ valuationOf q 275 = true := by
  have hs : count275 q = (countLit q [140]) + (countLit q [141]) := List.countP_append (p := literal q) (l₁ := [140]) (l₂ := [141])
  have hm := merge_left (literal (valuationOf q) (140)) (literal (valuationOf q) (275)) (countLit q [140]) (countLit q [141]) (count275 q) 1 (meaning140 q) (meaning275 q) hs
  change valuationOf q 140 = false ∨ valuationOf q 275 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause936 (q : Snake 81) (h : Conditions q) : valuation q 140 = false ∨ valuation q 275 = true := counterClause936 (baseVal q)

theorem counterClause937 (q : Nat → Bool) : valuationOf q 142 = false ∨ valuationOf q 277 = true := by
  have hs : count277 q = (countLit q [142]) + (countLit q [143]) := List.countP_append (p := literal q) (l₁ := [142]) (l₂ := [143])
  have hm := merge_left (literal (valuationOf q) (142)) (literal (valuationOf q) (277)) (countLit q [142]) (countLit q [143]) (count277 q) 1 (meaning142 q) (meaning277 q) hs
  change valuationOf q 142 = false ∨ valuationOf q 277 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause937 (q : Snake 81) (h : Conditions q) : valuation q 142 = false ∨ valuation q 277 = true := counterClause937 (baseVal q)

theorem counterClause938 (q : Nat → Bool) : valuationOf q 277 = false ∨ valuationOf q 279 = true := by
  have hs : count279 q = (countLit q [140, 141]) + (countLit q [142, 143]) := List.countP_append (p := literal q) (l₁ := [140, 141]) (l₂ := [142, 143])
  have hm := merge_right (literal (valuationOf q) (277)) (literal (valuationOf q) (279)) (countLit q [140, 141]) (countLit q [142, 143]) (count279 q) 1 (meaning277 q) (meaning279 q) hs
  change valuationOf q 277 = false ∨ valuationOf q 279 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause938 (q : Snake 81) (h : Conditions q) : valuation q 277 = false ∨ valuation q 279 = true := counterClause938 (baseVal q)

theorem counterClause939 (q : Nat → Bool) : valuationOf q 275 = false ∨ valuationOf q 279 = true := by
  have hs : count279 q = (countLit q [140, 141]) + (countLit q [142, 143]) := List.countP_append (p := literal q) (l₁ := [140, 141]) (l₂ := [142, 143])
  have hm := merge_left (literal (valuationOf q) (275)) (literal (valuationOf q) (279)) (countLit q [140, 141]) (countLit q [142, 143]) (count279 q) 1 (meaning275 q) (meaning279 q) hs
  change valuationOf q 275 = false ∨ valuationOf q 279 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause939 (q : Snake 81) (h : Conditions q) : valuation q 275 = false ∨ valuation q 279 = true := counterClause939 (baseVal q)

theorem counterClause940 (q : Nat → Bool) : valuationOf q 275 = false ∨ valuationOf q 277 = false ∨ valuationOf q 280 = true := by
  have hs : count279 q = (countLit q [140, 141]) + (countLit q [142, 143]) := List.countP_append (p := literal q) (l₁ := [140, 141]) (l₂ := [142, 143])
  have hm := merge_two (literal (valuationOf q) (275)) (literal (valuationOf q) (277)) (literal (valuationOf q) (280)) (countLit q [140, 141]) (countLit q [142, 143]) (count279 q) 1 1 (meaning275 q) (meaning277 q) (meaning280 q) hs
  change valuationOf q 275 = false ∨ valuationOf q 277 = false ∨ valuationOf q 280 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause940 (q : Snake 81) (h : Conditions q) : valuation q 275 = false ∨ valuation q 277 = false ∨ valuation q 280 = true := counterClause940 (baseVal q)

theorem counterClause941 (q : Nat → Bool) : valuationOf q 279 = false ∨ valuationOf q 281 = true := by
  have hs : count281 q = (countLit q [137, 138, 139]) + (countLit q [140, 141, 142, 143]) := List.countP_append (p := literal q) (l₁ := [137, 138, 139]) (l₂ := [140, 141, 142, 143])
  have hm := merge_right (literal (valuationOf q) (279)) (literal (valuationOf q) (281)) (countLit q [137, 138, 139]) (countLit q [140, 141, 142, 143]) (count281 q) 1 (meaning279 q) (meaning281 q) hs
  change valuationOf q 279 = false ∨ valuationOf q 281 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause941 (q : Snake 81) (h : Conditions q) : valuation q 279 = false ∨ valuation q 281 = true := counterClause941 (baseVal q)

theorem counterClause942 (q : Nat → Bool) : valuationOf q 280 = false ∨ valuationOf q 282 = true := by
  have hs : count281 q = (countLit q [137, 138, 139]) + (countLit q [140, 141, 142, 143]) := List.countP_append (p := literal q) (l₁ := [137, 138, 139]) (l₂ := [140, 141, 142, 143])
  have hm := merge_right (literal (valuationOf q) (280)) (literal (valuationOf q) (282)) (countLit q [137, 138, 139]) (countLit q [140, 141, 142, 143]) (count281 q) 2 (meaning280 q) (meaning282 q) hs
  change valuationOf q 280 = false ∨ valuationOf q 282 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause942 (q : Snake 81) (h : Conditions q) : valuation q 280 = false ∨ valuation q 282 = true := counterClause942 (baseVal q)

theorem counterClause943 (q : Nat → Bool) : valuationOf q 273 = false ∨ valuationOf q 281 = true := by
  have hs : count281 q = (countLit q [137, 138, 139]) + (countLit q [140, 141, 142, 143]) := List.countP_append (p := literal q) (l₁ := [137, 138, 139]) (l₂ := [140, 141, 142, 143])
  have hm := merge_left (literal (valuationOf q) (273)) (literal (valuationOf q) (281)) (countLit q [137, 138, 139]) (countLit q [140, 141, 142, 143]) (count281 q) 1 (meaning273 q) (meaning281 q) hs
  change valuationOf q 273 = false ∨ valuationOf q 281 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause943 (q : Snake 81) (h : Conditions q) : valuation q 273 = false ∨ valuation q 281 = true := counterClause943 (baseVal q)

theorem counterClause944 (q : Nat → Bool) : valuationOf q 273 = false ∨ valuationOf q 279 = false ∨ valuationOf q 282 = true := by
  have hs : count281 q = (countLit q [137, 138, 139]) + (countLit q [140, 141, 142, 143]) := List.countP_append (p := literal q) (l₁ := [137, 138, 139]) (l₂ := [140, 141, 142, 143])
  have hm := merge_two (literal (valuationOf q) (273)) (literal (valuationOf q) (279)) (literal (valuationOf q) (282)) (countLit q [137, 138, 139]) (countLit q [140, 141, 142, 143]) (count281 q) 1 1 (meaning273 q) (meaning279 q) (meaning282 q) hs
  change valuationOf q 273 = false ∨ valuationOf q 279 = false ∨ valuationOf q 282 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause944 (q : Snake 81) (h : Conditions q) : valuation q 273 = false ∨ valuation q 279 = false ∨ valuation q 282 = true := counterClause944 (baseVal q)

theorem counterClause945 (q : Nat → Bool) : valuationOf q 145 = false ∨ valuationOf q 283 = true := by
  have hs : count283 q = (countLit q [144]) + (countLit q [145]) := List.countP_append (p := literal q) (l₁ := [144]) (l₂ := [145])
  have hm := merge_right (literal (valuationOf q) (145)) (literal (valuationOf q) (283)) (countLit q [144]) (countLit q [145]) (count283 q) 1 (meaning145 q) (meaning283 q) hs
  change valuationOf q 145 = false ∨ valuationOf q 283 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause945 (q : Snake 81) (h : Conditions q) : valuation q 145 = false ∨ valuation q 283 = true := counterClause945 (baseVal q)

theorem counterClause946 (q : Nat → Bool) : valuationOf q 147 = false ∨ valuationOf q 285 = true := by
  have hs : count285 q = (countLit q [146]) + (countLit q [147]) := List.countP_append (p := literal q) (l₁ := [146]) (l₂ := [147])
  have hm := merge_right (literal (valuationOf q) (147)) (literal (valuationOf q) (285)) (countLit q [146]) (countLit q [147]) (count285 q) 1 (meaning147 q) (meaning285 q) hs
  change valuationOf q 147 = false ∨ valuationOf q 285 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause946 (q : Snake 81) (h : Conditions q) : valuation q 147 = false ∨ valuation q 285 = true := counterClause946 (baseVal q)

theorem counterClause947 (q : Nat → Bool) : valuationOf q 285 = false ∨ valuationOf q 287 = true := by
  have hs : count287 q = (countLit q [144, 145]) + (countLit q [146, 147]) := List.countP_append (p := literal q) (l₁ := [144, 145]) (l₂ := [146, 147])
  have hm := merge_right (literal (valuationOf q) (285)) (literal (valuationOf q) (287)) (countLit q [144, 145]) (countLit q [146, 147]) (count287 q) 1 (meaning285 q) (meaning287 q) hs
  change valuationOf q 285 = false ∨ valuationOf q 287 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause947 (q : Snake 81) (h : Conditions q) : valuation q 285 = false ∨ valuation q 287 = true := counterClause947 (baseVal q)

theorem counterClause948 (q : Nat → Bool) : valuationOf q 283 = false ∨ valuationOf q 287 = true := by
  have hs : count287 q = (countLit q [144, 145]) + (countLit q [146, 147]) := List.countP_append (p := literal q) (l₁ := [144, 145]) (l₂ := [146, 147])
  have hm := merge_left (literal (valuationOf q) (283)) (literal (valuationOf q) (287)) (countLit q [144, 145]) (countLit q [146, 147]) (count287 q) 1 (meaning283 q) (meaning287 q) hs
  change valuationOf q 283 = false ∨ valuationOf q 287 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause948 (q : Snake 81) (h : Conditions q) : valuation q 283 = false ∨ valuation q 287 = true := counterClause948 (baseVal q)

theorem counterClause949 (q : Nat → Bool) : valuationOf q 149 = false ∨ valuationOf q 289 = true := by
  have hs : count289 q = (countLit q [148]) + (countLit q [149]) := List.countP_append (p := literal q) (l₁ := [148]) (l₂ := [149])
  have hm := merge_right (literal (valuationOf q) (149)) (literal (valuationOf q) (289)) (countLit q [148]) (countLit q [149]) (count289 q) 1 (meaning149 q) (meaning289 q) hs
  change valuationOf q 149 = false ∨ valuationOf q 289 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause949 (q : Snake 81) (h : Conditions q) : valuation q 149 = false ∨ valuation q 289 = true := counterClause949 (baseVal q)

theorem counterClause950 (q : Nat → Bool) : valuationOf q 289 = false ∨ valuationOf q 293 = true := by
  have hs : count293 q = (countLit q [148, 149]) + (countLit q [150, 151]) := List.countP_append (p := literal q) (l₁ := [148, 149]) (l₂ := [150, 151])
  have hm := merge_left (literal (valuationOf q) (289)) (literal (valuationOf q) (293)) (countLit q [148, 149]) (countLit q [150, 151]) (count293 q) 1 (meaning289 q) (meaning293 q) hs
  change valuationOf q 289 = false ∨ valuationOf q 293 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause950 (q : Snake 81) (h : Conditions q) : valuation q 289 = false ∨ valuation q 293 = true := counterClause950 (baseVal q)

theorem counterClause951 (q : Nat → Bool) : valuationOf q 293 = false ∨ valuationOf q 295 = true := by
  have hs : count295 q = (countLit q [144, 145, 146, 147]) + (countLit q [148, 149, 150, 151]) := List.countP_append (p := literal q) (l₁ := [144, 145, 146, 147]) (l₂ := [148, 149, 150, 151])
  have hm := merge_right (literal (valuationOf q) (293)) (literal (valuationOf q) (295)) (countLit q [144, 145, 146, 147]) (countLit q [148, 149, 150, 151]) (count295 q) 1 (meaning293 q) (meaning295 q) hs
  change valuationOf q 293 = false ∨ valuationOf q 295 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause951 (q : Snake 81) (h : Conditions q) : valuation q 293 = false ∨ valuation q 295 = true := counterClause951 (baseVal q)

theorem counterClause952 (q : Nat → Bool) : valuationOf q 287 = false ∨ valuationOf q 295 = true := by
  have hs : count295 q = (countLit q [144, 145, 146, 147]) + (countLit q [148, 149, 150, 151]) := List.countP_append (p := literal q) (l₁ := [144, 145, 146, 147]) (l₂ := [148, 149, 150, 151])
  have hm := merge_left (literal (valuationOf q) (287)) (literal (valuationOf q) (295)) (countLit q [144, 145, 146, 147]) (countLit q [148, 149, 150, 151]) (count295 q) 1 (meaning287 q) (meaning295 q) hs
  change valuationOf q 287 = false ∨ valuationOf q 295 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause952 (q : Snake 81) (h : Conditions q) : valuation q 287 = false ∨ valuation q 295 = true := counterClause952 (baseVal q)

theorem counterClause953 (q : Nat → Bool) : valuationOf q 287 = false ∨ valuationOf q 293 = false ∨ valuationOf q 296 = true := by
  have hs : count295 q = (countLit q [144, 145, 146, 147]) + (countLit q [148, 149, 150, 151]) := List.countP_append (p := literal q) (l₁ := [144, 145, 146, 147]) (l₂ := [148, 149, 150, 151])
  have hm := merge_two (literal (valuationOf q) (287)) (literal (valuationOf q) (293)) (literal (valuationOf q) (296)) (countLit q [144, 145, 146, 147]) (countLit q [148, 149, 150, 151]) (count295 q) 1 1 (meaning287 q) (meaning293 q) (meaning296 q) hs
  change valuationOf q 287 = false ∨ valuationOf q 293 = false ∨ valuationOf q 296 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause953 (q : Snake 81) (h : Conditions q) : valuation q 287 = false ∨ valuation q 293 = false ∨ valuation q 296 = true := counterClause953 (baseVal q)

theorem counterClause954 (q : Nat → Bool) : valuationOf q 295 = false ∨ valuationOf q 297 = true := by
  have hs : count297 q = (countLit q [137, 138, 139, 140, 141, 142, 143]) + (countLit q [144, 145, 146, 147, 148, 149, 150, 151]) := List.countP_append (p := literal q) (l₁ := [137, 138, 139, 140, 141, 142, 143]) (l₂ := [144, 145, 146, 147, 148, 149, 150, 151])
  have hm := merge_right (literal (valuationOf q) (295)) (literal (valuationOf q) (297)) (countLit q [137, 138, 139, 140, 141, 142, 143]) (countLit q [144, 145, 146, 147, 148, 149, 150, 151]) (count297 q) 1 (meaning295 q) (meaning297 q) hs
  change valuationOf q 295 = false ∨ valuationOf q 297 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause954 (q : Snake 81) (h : Conditions q) : valuation q 295 = false ∨ valuation q 297 = true := counterClause954 (baseVal q)

theorem counterClause955 (q : Nat → Bool) : valuationOf q 296 = false ∨ valuationOf q 298 = true := by
  have hs : count297 q = (countLit q [137, 138, 139, 140, 141, 142, 143]) + (countLit q [144, 145, 146, 147, 148, 149, 150, 151]) := List.countP_append (p := literal q) (l₁ := [137, 138, 139, 140, 141, 142, 143]) (l₂ := [144, 145, 146, 147, 148, 149, 150, 151])
  have hm := merge_right (literal (valuationOf q) (296)) (literal (valuationOf q) (298)) (countLit q [137, 138, 139, 140, 141, 142, 143]) (countLit q [144, 145, 146, 147, 148, 149, 150, 151]) (count297 q) 2 (meaning296 q) (meaning298 q) hs
  change valuationOf q 296 = false ∨ valuationOf q 298 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause955 (q : Snake 81) (h : Conditions q) : valuation q 296 = false ∨ valuation q 298 = true := counterClause955 (baseVal q)

theorem counterClause956 (q : Nat → Bool) : valuationOf q 281 = false ∨ valuationOf q 297 = true := by
  have hs : count297 q = (countLit q [137, 138, 139, 140, 141, 142, 143]) + (countLit q [144, 145, 146, 147, 148, 149, 150, 151]) := List.countP_append (p := literal q) (l₁ := [137, 138, 139, 140, 141, 142, 143]) (l₂ := [144, 145, 146, 147, 148, 149, 150, 151])
  have hm := merge_left (literal (valuationOf q) (281)) (literal (valuationOf q) (297)) (countLit q [137, 138, 139, 140, 141, 142, 143]) (countLit q [144, 145, 146, 147, 148, 149, 150, 151]) (count297 q) 1 (meaning281 q) (meaning297 q) hs
  change valuationOf q 281 = false ∨ valuationOf q 297 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause956 (q : Snake 81) (h : Conditions q) : valuation q 281 = false ∨ valuation q 297 = true := counterClause956 (baseVal q)

theorem counterClause957 (q : Nat → Bool) : valuationOf q 282 = false ∨ valuationOf q 298 = true := by
  have hs : count297 q = (countLit q [137, 138, 139, 140, 141, 142, 143]) + (countLit q [144, 145, 146, 147, 148, 149, 150, 151]) := List.countP_append (p := literal q) (l₁ := [137, 138, 139, 140, 141, 142, 143]) (l₂ := [144, 145, 146, 147, 148, 149, 150, 151])
  have hm := merge_left (literal (valuationOf q) (282)) (literal (valuationOf q) (298)) (countLit q [137, 138, 139, 140, 141, 142, 143]) (countLit q [144, 145, 146, 147, 148, 149, 150, 151]) (count297 q) 2 (meaning282 q) (meaning298 q) hs
  change valuationOf q 282 = false ∨ valuationOf q 298 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause957 (q : Snake 81) (h : Conditions q) : valuation q 282 = false ∨ valuation q 298 = true := counterClause957 (baseVal q)

theorem counterClause958 (q : Nat → Bool) : valuationOf q 297 = false ∨ valuationOf q 299 = true := by
  have hs : count299 q = (countLit q [122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136]) + (countLit q [137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151]) := List.countP_append (p := literal q) (l₁ := [122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136]) (l₂ := [137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151])
  have hm := merge_right (literal (valuationOf q) (297)) (literal (valuationOf q) (299)) (countLit q [122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136]) (countLit q [137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151]) (count299 q) 1 (meaning297 q) (meaning299 q) hs
  change valuationOf q 297 = false ∨ valuationOf q 299 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause958 (q : Snake 81) (h : Conditions q) : valuation q 297 = false ∨ valuation q 299 = true := counterClause958 (baseVal q)

theorem counterClause959 (q : Nat → Bool) : valuationOf q 298 = false ∨ valuationOf q 300 = true := by
  have hs : count299 q = (countLit q [122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136]) + (countLit q [137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151]) := List.countP_append (p := literal q) (l₁ := [122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136]) (l₂ := [137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151])
  have hm := merge_right (literal (valuationOf q) (298)) (literal (valuationOf q) (300)) (countLit q [122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136]) (countLit q [137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151]) (count299 q) 2 (meaning298 q) (meaning300 q) hs
  change valuationOf q 298 = false ∨ valuationOf q 300 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause959 (q : Snake 81) (h : Conditions q) : valuation q 298 = false ∨ valuation q 300 = true := counterClause959 (baseVal q)

theorem counterClause960 (q : Nat → Bool) : valuationOf q 269 = false ∨ valuationOf q 299 = true := by
  have hs : count299 q = (countLit q [122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136]) + (countLit q [137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151]) := List.countP_append (p := literal q) (l₁ := [122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136]) (l₂ := [137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151])
  have hm := merge_left (literal (valuationOf q) (269)) (literal (valuationOf q) (299)) (countLit q [122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136]) (countLit q [137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151]) (count299 q) 1 (meaning269 q) (meaning299 q) hs
  change valuationOf q 269 = false ∨ valuationOf q 299 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause960 (q : Snake 81) (h : Conditions q) : valuation q 269 = false ∨ valuation q 299 = true := counterClause960 (baseVal q)

theorem block29 (q : Snake 81) (h : Conditions q) : B112E019.Block29 (valuation q) :=
  ⟨clause929 q h, clause930 q h, clause931 q h, clause932 q h, clause933 q h, clause934 q h, clause935 q h, clause936 q h, clause937 q h, clause938 q h, clause939 q h, clause940 q h, clause941 q h, clause942 q h, clause943 q h, clause944 q h, clause945 q h, clause946 q h, clause947 q h, clause948 q h, clause949 q h, clause950 q h, clause951 q h, clause952 q h, clause953 q h, clause954 q h, clause955 q h, clause956 q h, clause957 q h, clause958 q h, clause959 q h, clause960 q h⟩

end
end Snake9.Regrowth.E112019
