import E112057Semantics
import B112E057Inputs
namespace Snake9.Regrowth.E112057
noncomputable section
local instance blockDec32 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause1025 (q : Snake 81) (h : Conditions q) : valuation q 245 = false := by
  rw [value245]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (401 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause1026 (q : Snake 81) (h : Conditions q) : valuation q 248 = false := by
  rw [value248]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (407 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause1027 (q : Snake 81) (h : Conditions q) : valuation q 250 = false := by
  rw [value250]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (411 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause1028 (q : Snake 81) (h : Conditions q) : valuation q 252 = false := by
  rw [value252]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (414 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem counterClause1029 (q : Nat → Bool) : valuationOf q 130 = false ∨ valuationOf q 255 = true := by
  have hs : count255 q = (countLit q [129]) + (countLit q [130]) := List.countP_append (p := literal q) (l₁ := [129]) (l₂ := [130])
  have hm := merge_right (literal (valuationOf q) (130)) (literal (valuationOf q) (255)) (countLit q [129]) (countLit q [130]) (count255 q) 1 (meaning130 q) (meaning255 q) hs
  change valuationOf q 130 = false ∨ valuationOf q 255 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1029 (q : Snake 81) (h : Conditions q) : valuation q 130 = false ∨ valuation q 255 = true := counterClause1029 (baseVal q)

theorem counterClause1030 (q : Nat → Bool) : valuationOf q 129 = false ∨ valuationOf q 255 = true := by
  have hs : count255 q = (countLit q [129]) + (countLit q [130]) := List.countP_append (p := literal q) (l₁ := [129]) (l₂ := [130])
  have hm := merge_left (literal (valuationOf q) (129)) (literal (valuationOf q) (255)) (countLit q [129]) (countLit q [130]) (count255 q) 1 (meaning129 q) (meaning255 q) hs
  change valuationOf q 129 = false ∨ valuationOf q 255 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1030 (q : Snake 81) (h : Conditions q) : valuation q 129 = false ∨ valuation q 255 = true := counterClause1030 (baseVal q)

theorem counterClause1031 (q : Nat → Bool) : valuationOf q 255 = false ∨ valuationOf q 257 = true := by
  have hs : count257 q = (countLit q [128]) + (countLit q [129, 130]) := List.countP_append (p := literal q) (l₁ := [128]) (l₂ := [129, 130])
  have hm := merge_right (literal (valuationOf q) (255)) (literal (valuationOf q) (257)) (countLit q [128]) (countLit q [129, 130]) (count257 q) 1 (meaning255 q) (meaning257 q) hs
  change valuationOf q 255 = false ∨ valuationOf q 257 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1031 (q : Snake 81) (h : Conditions q) : valuation q 255 = false ∨ valuation q 257 = true := counterClause1031 (baseVal q)

theorem counterClause1032 (q : Nat → Bool) : valuationOf q 257 = false ∨ valuationOf q 265 = true := by
  have hs : count265 q = (countLit q [128, 129, 130]) + (countLit q [131, 132, 133, 134]) := List.countP_append (p := literal q) (l₁ := [128, 129, 130]) (l₂ := [131, 132, 133, 134])
  have hm := merge_left (literal (valuationOf q) (257)) (literal (valuationOf q) (265)) (countLit q [128, 129, 130]) (countLit q [131, 132, 133, 134]) (count265 q) 1 (meaning257 q) (meaning265 q) hs
  change valuationOf q 257 = false ∨ valuationOf q 265 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1032 (q : Snake 81) (h : Conditions q) : valuation q 257 = false ∨ valuation q 265 = true := counterClause1032 (baseVal q)

theorem counterClause1033 (q : Nat → Bool) : valuationOf q 135 = false ∨ valuationOf q 267 = true := by
  have hs : count267 q = (countLit q [135]) + (countLit q [136]) := List.countP_append (p := literal q) (l₁ := [135]) (l₂ := [136])
  have hm := merge_left (literal (valuationOf q) (135)) (literal (valuationOf q) (267)) (countLit q [135]) (countLit q [136]) (count267 q) 1 (meaning135 q) (meaning267 q) hs
  change valuationOf q 135 = false ∨ valuationOf q 267 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1033 (q : Snake 81) (h : Conditions q) : valuation q 135 = false ∨ valuation q 267 = true := counterClause1033 (baseVal q)

theorem counterClause1034 (q : Nat → Bool) : valuationOf q 267 = false ∨ valuationOf q 271 = true := by
  have hs : count271 q = (countLit q [135, 136]) + (countLit q [137, 138]) := List.countP_append (p := literal q) (l₁ := [135, 136]) (l₂ := [137, 138])
  have hm := merge_left (literal (valuationOf q) (267)) (literal (valuationOf q) (271)) (countLit q [135, 136]) (countLit q [137, 138]) (count271 q) 1 (meaning267 q) (meaning271 q) hs
  change valuationOf q 267 = false ∨ valuationOf q 271 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1034 (q : Snake 81) (h : Conditions q) : valuation q 267 = false ∨ valuation q 271 = true := counterClause1034 (baseVal q)

theorem counterClause1035 (q : Nat → Bool) : valuationOf q 140 = false ∨ valuationOf q 273 = true := by
  have hs : count273 q = (countLit q [139]) + (countLit q [140]) := List.countP_append (p := literal q) (l₁ := [139]) (l₂ := [140])
  have hm := merge_right (literal (valuationOf q) (140)) (literal (valuationOf q) (273)) (countLit q [139]) (countLit q [140]) (count273 q) 1 (meaning140 q) (meaning273 q) hs
  change valuationOf q 140 = false ∨ valuationOf q 273 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1035 (q : Snake 81) (h : Conditions q) : valuation q 140 = false ∨ valuation q 273 = true := counterClause1035 (baseVal q)

theorem counterClause1036 (q : Nat → Bool) : valuationOf q 139 = false ∨ valuationOf q 273 = true := by
  have hs : count273 q = (countLit q [139]) + (countLit q [140]) := List.countP_append (p := literal q) (l₁ := [139]) (l₂ := [140])
  have hm := merge_left (literal (valuationOf q) (139)) (literal (valuationOf q) (273)) (countLit q [139]) (countLit q [140]) (count273 q) 1 (meaning139 q) (meaning273 q) hs
  change valuationOf q 139 = false ∨ valuationOf q 273 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1036 (q : Snake 81) (h : Conditions q) : valuation q 139 = false ∨ valuation q 273 = true := counterClause1036 (baseVal q)

theorem counterClause1037 (q : Nat → Bool) : valuationOf q 141 = false ∨ valuationOf q 275 = true := by
  have hs : count275 q = (countLit q [141]) + (countLit q [142]) := List.countP_append (p := literal q) (l₁ := [141]) (l₂ := [142])
  have hm := merge_left (literal (valuationOf q) (141)) (literal (valuationOf q) (275)) (countLit q [141]) (countLit q [142]) (count275 q) 1 (meaning141 q) (meaning275 q) hs
  change valuationOf q 141 = false ∨ valuationOf q 275 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1037 (q : Snake 81) (h : Conditions q) : valuation q 141 = false ∨ valuation q 275 = true := counterClause1037 (baseVal q)

theorem counterClause1038 (q : Nat → Bool) : valuationOf q 275 = false ∨ valuationOf q 277 = true := by
  have hs : count277 q = (countLit q [139, 140]) + (countLit q [141, 142]) := List.countP_append (p := literal q) (l₁ := [139, 140]) (l₂ := [141, 142])
  have hm := merge_right (literal (valuationOf q) (275)) (literal (valuationOf q) (277)) (countLit q [139, 140]) (countLit q [141, 142]) (count277 q) 1 (meaning275 q) (meaning277 q) hs
  change valuationOf q 275 = false ∨ valuationOf q 277 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1038 (q : Snake 81) (h : Conditions q) : valuation q 275 = false ∨ valuation q 277 = true := counterClause1038 (baseVal q)

theorem counterClause1039 (q : Nat → Bool) : valuationOf q 273 = false ∨ valuationOf q 277 = true := by
  have hs : count277 q = (countLit q [139, 140]) + (countLit q [141, 142]) := List.countP_append (p := literal q) (l₁ := [139, 140]) (l₂ := [141, 142])
  have hm := merge_left (literal (valuationOf q) (273)) (literal (valuationOf q) (277)) (countLit q [139, 140]) (countLit q [141, 142]) (count277 q) 1 (meaning273 q) (meaning277 q) hs
  change valuationOf q 273 = false ∨ valuationOf q 277 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1039 (q : Snake 81) (h : Conditions q) : valuation q 273 = false ∨ valuation q 277 = true := counterClause1039 (baseVal q)

theorem counterClause1040 (q : Nat → Bool) : valuationOf q 277 = false ∨ valuationOf q 279 = true := by
  have hs : count279 q = (countLit q [135, 136, 137, 138]) + (countLit q [139, 140, 141, 142]) := List.countP_append (p := literal q) (l₁ := [135, 136, 137, 138]) (l₂ := [139, 140, 141, 142])
  have hm := merge_right (literal (valuationOf q) (277)) (literal (valuationOf q) (279)) (countLit q [135, 136, 137, 138]) (countLit q [139, 140, 141, 142]) (count279 q) 1 (meaning277 q) (meaning279 q) hs
  change valuationOf q 277 = false ∨ valuationOf q 279 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1040 (q : Snake 81) (h : Conditions q) : valuation q 277 = false ∨ valuation q 279 = true := counterClause1040 (baseVal q)

theorem counterClause1041 (q : Nat → Bool) : valuationOf q 271 = false ∨ valuationOf q 279 = true := by
  have hs : count279 q = (countLit q [135, 136, 137, 138]) + (countLit q [139, 140, 141, 142]) := List.countP_append (p := literal q) (l₁ := [135, 136, 137, 138]) (l₂ := [139, 140, 141, 142])
  have hm := merge_left (literal (valuationOf q) (271)) (literal (valuationOf q) (279)) (countLit q [135, 136, 137, 138]) (countLit q [139, 140, 141, 142]) (count279 q) 1 (meaning271 q) (meaning279 q) hs
  change valuationOf q 271 = false ∨ valuationOf q 279 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1041 (q : Snake 81) (h : Conditions q) : valuation q 271 = false ∨ valuation q 279 = true := counterClause1041 (baseVal q)

theorem counterClause1042 (q : Nat → Bool) : valuationOf q 279 = false ∨ valuationOf q 281 = true := by
  have hs : count281 q = (countLit q [128, 129, 130, 131, 132, 133, 134]) + (countLit q [135, 136, 137, 138, 139, 140, 141, 142]) := List.countP_append (p := literal q) (l₁ := [128, 129, 130, 131, 132, 133, 134]) (l₂ := [135, 136, 137, 138, 139, 140, 141, 142])
  have hm := merge_right (literal (valuationOf q) (279)) (literal (valuationOf q) (281)) (countLit q [128, 129, 130, 131, 132, 133, 134]) (countLit q [135, 136, 137, 138, 139, 140, 141, 142]) (count281 q) 1 (meaning279 q) (meaning281 q) hs
  change valuationOf q 279 = false ∨ valuationOf q 281 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1042 (q : Snake 81) (h : Conditions q) : valuation q 279 = false ∨ valuation q 281 = true := counterClause1042 (baseVal q)

theorem counterClause1043 (q : Nat → Bool) : valuationOf q 265 = false ∨ valuationOf q 281 = true := by
  have hs : count281 q = (countLit q [128, 129, 130, 131, 132, 133, 134]) + (countLit q [135, 136, 137, 138, 139, 140, 141, 142]) := List.countP_append (p := literal q) (l₁ := [128, 129, 130, 131, 132, 133, 134]) (l₂ := [135, 136, 137, 138, 139, 140, 141, 142])
  have hm := merge_left (literal (valuationOf q) (265)) (literal (valuationOf q) (281)) (countLit q [128, 129, 130, 131, 132, 133, 134]) (countLit q [135, 136, 137, 138, 139, 140, 141, 142]) (count281 q) 1 (meaning265 q) (meaning281 q) hs
  change valuationOf q 265 = false ∨ valuationOf q 281 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1043 (q : Snake 81) (h : Conditions q) : valuation q 265 = false ∨ valuation q 281 = true := counterClause1043 (baseVal q)

theorem counterClause1044 (q : Nat → Bool) : valuationOf q 265 = false ∨ valuationOf q 279 = false ∨ valuationOf q 282 = true := by
  have hs : count281 q = (countLit q [128, 129, 130, 131, 132, 133, 134]) + (countLit q [135, 136, 137, 138, 139, 140, 141, 142]) := List.countP_append (p := literal q) (l₁ := [128, 129, 130, 131, 132, 133, 134]) (l₂ := [135, 136, 137, 138, 139, 140, 141, 142])
  have hm := merge_two (literal (valuationOf q) (265)) (literal (valuationOf q) (279)) (literal (valuationOf q) (282)) (countLit q [128, 129, 130, 131, 132, 133, 134]) (countLit q [135, 136, 137, 138, 139, 140, 141, 142]) (count281 q) 1 1 (meaning265 q) (meaning279 q) (meaning282 q) hs
  change valuationOf q 265 = false ∨ valuationOf q 279 = false ∨ valuationOf q 282 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1044 (q : Snake 81) (h : Conditions q) : valuation q 265 = false ∨ valuation q 279 = false ∨ valuation q 282 = true := counterClause1044 (baseVal q)

theorem counterClause1045 (q : Nat → Bool) : valuationOf q 143 = false ∨ valuationOf q 283 = true := by
  have hs : count283 q = (countLit q [143]) + (countLit q [144]) := List.countP_append (p := literal q) (l₁ := [143]) (l₂ := [144])
  have hm := merge_left (literal (valuationOf q) (143)) (literal (valuationOf q) (283)) (countLit q [143]) (countLit q [144]) (count283 q) 1 (meaning143 q) (meaning283 q) hs
  change valuationOf q 143 = false ∨ valuationOf q 283 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1045 (q : Snake 81) (h : Conditions q) : valuation q 143 = false ∨ valuation q 283 = true := counterClause1045 (baseVal q)

theorem counterClause1046 (q : Nat → Bool) : valuationOf q 145 = false ∨ valuationOf q 285 = true := by
  have hs : count285 q = (countLit q [145]) + (countLit q [146]) := List.countP_append (p := literal q) (l₁ := [145]) (l₂ := [146])
  have hm := merge_left (literal (valuationOf q) (145)) (literal (valuationOf q) (285)) (countLit q [145]) (countLit q [146]) (count285 q) 1 (meaning145 q) (meaning285 q) hs
  change valuationOf q 145 = false ∨ valuationOf q 285 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1046 (q : Snake 81) (h : Conditions q) : valuation q 145 = false ∨ valuation q 285 = true := counterClause1046 (baseVal q)

theorem counterClause1047 (q : Nat → Bool) : valuationOf q 285 = false ∨ valuationOf q 287 = true := by
  have hs : count287 q = (countLit q [143, 144]) + (countLit q [145, 146]) := List.countP_append (p := literal q) (l₁ := [143, 144]) (l₂ := [145, 146])
  have hm := merge_right (literal (valuationOf q) (285)) (literal (valuationOf q) (287)) (countLit q [143, 144]) (countLit q [145, 146]) (count287 q) 1 (meaning285 q) (meaning287 q) hs
  change valuationOf q 285 = false ∨ valuationOf q 287 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1047 (q : Snake 81) (h : Conditions q) : valuation q 285 = false ∨ valuation q 287 = true := counterClause1047 (baseVal q)

theorem counterClause1048 (q : Nat → Bool) : valuationOf q 283 = false ∨ valuationOf q 287 = true := by
  have hs : count287 q = (countLit q [143, 144]) + (countLit q [145, 146]) := List.countP_append (p := literal q) (l₁ := [143, 144]) (l₂ := [145, 146])
  have hm := merge_left (literal (valuationOf q) (283)) (literal (valuationOf q) (287)) (countLit q [143, 144]) (countLit q [145, 146]) (count287 q) 1 (meaning283 q) (meaning287 q) hs
  change valuationOf q 283 = false ∨ valuationOf q 287 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1048 (q : Snake 81) (h : Conditions q) : valuation q 283 = false ∨ valuation q 287 = true := counterClause1048 (baseVal q)

theorem counterClause1049 (q : Nat → Bool) : valuationOf q 283 = false ∨ valuationOf q 285 = false ∨ valuationOf q 288 = true := by
  have hs : count287 q = (countLit q [143, 144]) + (countLit q [145, 146]) := List.countP_append (p := literal q) (l₁ := [143, 144]) (l₂ := [145, 146])
  have hm := merge_two (literal (valuationOf q) (283)) (literal (valuationOf q) (285)) (literal (valuationOf q) (288)) (countLit q [143, 144]) (countLit q [145, 146]) (count287 q) 1 1 (meaning283 q) (meaning285 q) (meaning288 q) hs
  change valuationOf q 283 = false ∨ valuationOf q 285 = false ∨ valuationOf q 288 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1049 (q : Snake 81) (h : Conditions q) : valuation q 283 = false ∨ valuation q 285 = false ∨ valuation q 288 = true := counterClause1049 (baseVal q)

theorem counterClause1050 (q : Nat → Bool) : valuationOf q 148 = false ∨ valuationOf q 289 = true := by
  have hs : count289 q = (countLit q [147]) + (countLit q [148]) := List.countP_append (p := literal q) (l₁ := [147]) (l₂ := [148])
  have hm := merge_right (literal (valuationOf q) (148)) (literal (valuationOf q) (289)) (countLit q [147]) (countLit q [148]) (count289 q) 1 (meaning148 q) (meaning289 q) hs
  change valuationOf q 148 = false ∨ valuationOf q 289 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1050 (q : Snake 81) (h : Conditions q) : valuation q 148 = false ∨ valuation q 289 = true := counterClause1050 (baseVal q)

theorem counterClause1051 (q : Nat → Bool) : valuationOf q 147 = false ∨ valuationOf q 289 = true := by
  have hs : count289 q = (countLit q [147]) + (countLit q [148]) := List.countP_append (p := literal q) (l₁ := [147]) (l₂ := [148])
  have hm := merge_left (literal (valuationOf q) (147)) (literal (valuationOf q) (289)) (countLit q [147]) (countLit q [148]) (count289 q) 1 (meaning147 q) (meaning289 q) hs
  change valuationOf q 147 = false ∨ valuationOf q 289 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1051 (q : Snake 81) (h : Conditions q) : valuation q 147 = false ∨ valuation q 289 = true := counterClause1051 (baseVal q)

theorem counterClause1052 (q : Nat → Bool) : valuationOf q 150 = false ∨ valuationOf q 291 = true := by
  have hs : count291 q = (countLit q [149]) + (countLit q [150]) := List.countP_append (p := literal q) (l₁ := [149]) (l₂ := [150])
  have hm := merge_right (literal (valuationOf q) (150)) (literal (valuationOf q) (291)) (countLit q [149]) (countLit q [150]) (count291 q) 1 (meaning150 q) (meaning291 q) hs
  change valuationOf q 150 = false ∨ valuationOf q 291 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1052 (q : Snake 81) (h : Conditions q) : valuation q 150 = false ∨ valuation q 291 = true := counterClause1052 (baseVal q)

theorem counterClause1053 (q : Nat → Bool) : valuationOf q 291 = false ∨ valuationOf q 293 = true := by
  have hs : count293 q = (countLit q [147, 148]) + (countLit q [149, 150]) := List.countP_append (p := literal q) (l₁ := [147, 148]) (l₂ := [149, 150])
  have hm := merge_right (literal (valuationOf q) (291)) (literal (valuationOf q) (293)) (countLit q [147, 148]) (countLit q [149, 150]) (count293 q) 1 (meaning291 q) (meaning293 q) hs
  change valuationOf q 291 = false ∨ valuationOf q 293 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1053 (q : Snake 81) (h : Conditions q) : valuation q 291 = false ∨ valuation q 293 = true := counterClause1053 (baseVal q)

theorem counterClause1054 (q : Nat → Bool) : valuationOf q 289 = false ∨ valuationOf q 293 = true := by
  have hs : count293 q = (countLit q [147, 148]) + (countLit q [149, 150]) := List.countP_append (p := literal q) (l₁ := [147, 148]) (l₂ := [149, 150])
  have hm := merge_left (literal (valuationOf q) (289)) (literal (valuationOf q) (293)) (countLit q [147, 148]) (countLit q [149, 150]) (count293 q) 1 (meaning289 q) (meaning293 q) hs
  change valuationOf q 289 = false ∨ valuationOf q 293 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1054 (q : Snake 81) (h : Conditions q) : valuation q 289 = false ∨ valuation q 293 = true := counterClause1054 (baseVal q)

theorem counterClause1055 (q : Nat → Bool) : valuationOf q 293 = false ∨ valuationOf q 295 = true := by
  have hs : count295 q = (countLit q [143, 144, 145, 146]) + (countLit q [147, 148, 149, 150]) := List.countP_append (p := literal q) (l₁ := [143, 144, 145, 146]) (l₂ := [147, 148, 149, 150])
  have hm := merge_right (literal (valuationOf q) (293)) (literal (valuationOf q) (295)) (countLit q [143, 144, 145, 146]) (countLit q [147, 148, 149, 150]) (count295 q) 1 (meaning293 q) (meaning295 q) hs
  change valuationOf q 293 = false ∨ valuationOf q 295 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1055 (q : Snake 81) (h : Conditions q) : valuation q 293 = false ∨ valuation q 295 = true := counterClause1055 (baseVal q)

theorem counterClause1056 (q : Nat → Bool) : valuationOf q 287 = false ∨ valuationOf q 295 = true := by
  have hs : count295 q = (countLit q [143, 144, 145, 146]) + (countLit q [147, 148, 149, 150]) := List.countP_append (p := literal q) (l₁ := [143, 144, 145, 146]) (l₂ := [147, 148, 149, 150])
  have hm := merge_left (literal (valuationOf q) (287)) (literal (valuationOf q) (295)) (countLit q [143, 144, 145, 146]) (countLit q [147, 148, 149, 150]) (count295 q) 1 (meaning287 q) (meaning295 q) hs
  change valuationOf q 287 = false ∨ valuationOf q 295 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1056 (q : Snake 81) (h : Conditions q) : valuation q 287 = false ∨ valuation q 295 = true := counterClause1056 (baseVal q)

theorem block32 (q : Snake 81) (h : Conditions q) : B112E057.Block32 (valuation q) :=
  ⟨clause1025 q h, clause1026 q h, clause1027 q h, clause1028 q h, clause1029 q h, clause1030 q h, clause1031 q h, clause1032 q h, clause1033 q h, clause1034 q h, clause1035 q h, clause1036 q h, clause1037 q h, clause1038 q h, clause1039 q h, clause1040 q h, clause1041 q h, clause1042 q h, clause1043 q h, clause1044 q h, clause1045 q h, clause1046 q h, clause1047 q h, clause1048 q h, clause1049 q h, clause1050 q h, clause1051 q h, clause1052 q h, clause1053 q h, clause1054 q h, clause1055 q h, clause1056 q h⟩

end
end Snake9.Regrowth.E112057
