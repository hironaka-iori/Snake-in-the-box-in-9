import E112052Semantics
import B112E052Inputs
namespace Snake9.Regrowth.E112052
noncomputable section
local instance blockDec32 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause1025 (q : Snake 81) (h : Conditions q) : valuation q 245 = false := by
  rw [value245]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (463 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause1026 (q : Snake 81) (h : Conditions q) : valuation q 247 = false := by
  rw [value247]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (466 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause1027 (q : Snake 81) (h : Conditions q) : valuation q 249 = false := by
  rw [value249]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (471 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause1028 (q : Snake 81) (h : Conditions q) : valuation q 250 = false := by
  rw [value250]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (472 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause1029 (q : Snake 81) (h : Conditions q) : valuation q 253 = false := by
  rw [value253]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (477 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause1030 (q : Snake 81) (h : Conditions q) : valuation q 254 = false := by
  rw [value254]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (478 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem counterClause1031 (q : Nat → Bool) : valuationOf q 131 = false ∨ valuationOf q 255 = true := by
  have hs : count255 q = (countLit q [130]) + (countLit q [131]) := List.countP_append (p := literal q) (l₁ := [130]) (l₂ := [131])
  have hm := merge_right (literal (valuationOf q) (131)) (literal (valuationOf q) (255)) (countLit q [130]) (countLit q [131]) (count255 q) 1 (meaning131 q) (meaning255 q) hs
  change valuationOf q 131 = false ∨ valuationOf q 255 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1031 (q : Snake 81) (h : Conditions q) : valuation q 131 = false ∨ valuation q 255 = true := counterClause1031 (baseVal q)

theorem counterClause1032 (q : Nat → Bool) : valuationOf q 255 = false ∨ valuationOf q 257 = true := by
  have hs : count257 q = (countLit q [129]) + (countLit q [130, 131]) := List.countP_append (p := literal q) (l₁ := [129]) (l₂ := [130, 131])
  have hm := merge_right (literal (valuationOf q) (255)) (literal (valuationOf q) (257)) (countLit q [129]) (countLit q [130, 131]) (count257 q) 1 (meaning255 q) (meaning257 q) hs
  change valuationOf q 255 = false ∨ valuationOf q 257 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1032 (q : Snake 81) (h : Conditions q) : valuation q 255 = false ∨ valuation q 257 = true := counterClause1032 (baseVal q)

theorem counterClause1033 (q : Nat → Bool) : valuationOf q 129 = false ∨ valuationOf q 257 = true := by
  have hs : count257 q = (countLit q [129]) + (countLit q [130, 131]) := List.countP_append (p := literal q) (l₁ := [129]) (l₂ := [130, 131])
  have hm := merge_left (literal (valuationOf q) (129)) (literal (valuationOf q) (257)) (countLit q [129]) (countLit q [130, 131]) (count257 q) 1 (meaning129 q) (meaning257 q) hs
  change valuationOf q 129 = false ∨ valuationOf q 257 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1033 (q : Snake 81) (h : Conditions q) : valuation q 129 = false ∨ valuation q 257 = true := counterClause1033 (baseVal q)

theorem counterClause1034 (q : Nat → Bool) : valuationOf q 129 = false ∨ valuationOf q 255 = false ∨ valuationOf q 258 = true := by
  have hs : count257 q = (countLit q [129]) + (countLit q [130, 131]) := List.countP_append (p := literal q) (l₁ := [129]) (l₂ := [130, 131])
  have hm := merge_two (literal (valuationOf q) (129)) (literal (valuationOf q) (255)) (literal (valuationOf q) (258)) (countLit q [129]) (countLit q [130, 131]) (count257 q) 1 1 (meaning129 q) (meaning255 q) (meaning258 q) hs
  change valuationOf q 129 = false ∨ valuationOf q 255 = false ∨ valuationOf q 258 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1034 (q : Snake 81) (h : Conditions q) : valuation q 129 = false ∨ valuation q 255 = false ∨ valuation q 258 = true := counterClause1034 (baseVal q)

theorem counterClause1035 (q : Nat → Bool) : valuationOf q 133 = false ∨ valuationOf q 259 = true := by
  have hs : count259 q = (countLit q [132]) + (countLit q [133]) := List.countP_append (p := literal q) (l₁ := [132]) (l₂ := [133])
  have hm := merge_right (literal (valuationOf q) (133)) (literal (valuationOf q) (259)) (countLit q [132]) (countLit q [133]) (count259 q) 1 (meaning133 q) (meaning259 q) hs
  change valuationOf q 133 = false ∨ valuationOf q 259 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1035 (q : Snake 81) (h : Conditions q) : valuation q 133 = false ∨ valuation q 259 = true := counterClause1035 (baseVal q)

theorem counterClause1036 (q : Nat → Bool) : valuationOf q 259 = false ∨ valuationOf q 263 = true := by
  have hs : count263 q = (countLit q [132, 133]) + (countLit q [134, 135]) := List.countP_append (p := literal q) (l₁ := [132, 133]) (l₂ := [134, 135])
  have hm := merge_left (literal (valuationOf q) (259)) (literal (valuationOf q) (263)) (countLit q [132, 133]) (countLit q [134, 135]) (count263 q) 1 (meaning259 q) (meaning263 q) hs
  change valuationOf q 259 = false ∨ valuationOf q 263 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1036 (q : Snake 81) (h : Conditions q) : valuation q 259 = false ∨ valuation q 263 = true := counterClause1036 (baseVal q)

theorem counterClause1037 (q : Nat → Bool) : valuationOf q 263 = false ∨ valuationOf q 265 = true := by
  have hs : count265 q = (countLit q [129, 130, 131]) + (countLit q [132, 133, 134, 135]) := List.countP_append (p := literal q) (l₁ := [129, 130, 131]) (l₂ := [132, 133, 134, 135])
  have hm := merge_right (literal (valuationOf q) (263)) (literal (valuationOf q) (265)) (countLit q [129, 130, 131]) (countLit q [132, 133, 134, 135]) (count265 q) 1 (meaning263 q) (meaning265 q) hs
  change valuationOf q 263 = false ∨ valuationOf q 265 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1037 (q : Snake 81) (h : Conditions q) : valuation q 263 = false ∨ valuation q 265 = true := counterClause1037 (baseVal q)

theorem counterClause1038 (q : Nat → Bool) : valuationOf q 257 = false ∨ valuationOf q 265 = true := by
  have hs : count265 q = (countLit q [129, 130, 131]) + (countLit q [132, 133, 134, 135]) := List.countP_append (p := literal q) (l₁ := [129, 130, 131]) (l₂ := [132, 133, 134, 135])
  have hm := merge_left (literal (valuationOf q) (257)) (literal (valuationOf q) (265)) (countLit q [129, 130, 131]) (countLit q [132, 133, 134, 135]) (count265 q) 1 (meaning257 q) (meaning265 q) hs
  change valuationOf q 257 = false ∨ valuationOf q 265 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1038 (q : Snake 81) (h : Conditions q) : valuation q 257 = false ∨ valuation q 265 = true := counterClause1038 (baseVal q)

theorem counterClause1039 (q : Nat → Bool) : valuationOf q 257 = false ∨ valuationOf q 263 = false ∨ valuationOf q 266 = true := by
  have hs : count265 q = (countLit q [129, 130, 131]) + (countLit q [132, 133, 134, 135]) := List.countP_append (p := literal q) (l₁ := [129, 130, 131]) (l₂ := [132, 133, 134, 135])
  have hm := merge_two (literal (valuationOf q) (257)) (literal (valuationOf q) (263)) (literal (valuationOf q) (266)) (countLit q [129, 130, 131]) (countLit q [132, 133, 134, 135]) (count265 q) 1 1 (meaning257 q) (meaning263 q) (meaning266 q) hs
  change valuationOf q 257 = false ∨ valuationOf q 263 = false ∨ valuationOf q 266 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1039 (q : Snake 81) (h : Conditions q) : valuation q 257 = false ∨ valuation q 263 = false ∨ valuation q 266 = true := counterClause1039 (baseVal q)

theorem counterClause1040 (q : Nat → Bool) : valuationOf q 258 = false ∨ valuationOf q 266 = true := by
  have hs : count265 q = (countLit q [129, 130, 131]) + (countLit q [132, 133, 134, 135]) := List.countP_append (p := literal q) (l₁ := [129, 130, 131]) (l₂ := [132, 133, 134, 135])
  have hm := merge_left (literal (valuationOf q) (258)) (literal (valuationOf q) (266)) (countLit q [129, 130, 131]) (countLit q [132, 133, 134, 135]) (count265 q) 2 (meaning258 q) (meaning266 q) hs
  change valuationOf q 258 = false ∨ valuationOf q 266 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1040 (q : Snake 81) (h : Conditions q) : valuation q 258 = false ∨ valuation q 266 = true := counterClause1040 (baseVal q)

theorem counterClause1041 (q : Nat → Bool) : valuationOf q 136 = false ∨ valuationOf q 267 = true := by
  have hs : count267 q = (countLit q [136]) + (countLit q [137]) := List.countP_append (p := literal q) (l₁ := [136]) (l₂ := [137])
  have hm := merge_left (literal (valuationOf q) (136)) (literal (valuationOf q) (267)) (countLit q [136]) (countLit q [137]) (count267 q) 1 (meaning136 q) (meaning267 q) hs
  change valuationOf q 136 = false ∨ valuationOf q 267 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1041 (q : Snake 81) (h : Conditions q) : valuation q 136 = false ∨ valuation q 267 = true := counterClause1041 (baseVal q)

theorem counterClause1042 (q : Nat → Bool) : valuationOf q 267 = false ∨ valuationOf q 271 = true := by
  have hs : count271 q = (countLit q [136, 137]) + (countLit q [138, 139]) := List.countP_append (p := literal q) (l₁ := [136, 137]) (l₂ := [138, 139])
  have hm := merge_left (literal (valuationOf q) (267)) (literal (valuationOf q) (271)) (countLit q [136, 137]) (countLit q [138, 139]) (count271 q) 1 (meaning267 q) (meaning271 q) hs
  change valuationOf q 267 = false ∨ valuationOf q 271 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1042 (q : Snake 81) (h : Conditions q) : valuation q 267 = false ∨ valuation q 271 = true := counterClause1042 (baseVal q)

theorem counterClause1043 (q : Nat → Bool) : valuationOf q 141 = false ∨ valuationOf q 273 = true := by
  have hs : count273 q = (countLit q [140]) + (countLit q [141]) := List.countP_append (p := literal q) (l₁ := [140]) (l₂ := [141])
  have hm := merge_right (literal (valuationOf q) (141)) (literal (valuationOf q) (273)) (countLit q [140]) (countLit q [141]) (count273 q) 1 (meaning141 q) (meaning273 q) hs
  change valuationOf q 141 = false ∨ valuationOf q 273 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1043 (q : Snake 81) (h : Conditions q) : valuation q 141 = false ∨ valuation q 273 = true := counterClause1043 (baseVal q)

theorem counterClause1044 (q : Nat → Bool) : valuationOf q 140 = false ∨ valuationOf q 273 = true := by
  have hs : count273 q = (countLit q [140]) + (countLit q [141]) := List.countP_append (p := literal q) (l₁ := [140]) (l₂ := [141])
  have hm := merge_left (literal (valuationOf q) (140)) (literal (valuationOf q) (273)) (countLit q [140]) (countLit q [141]) (count273 q) 1 (meaning140 q) (meaning273 q) hs
  change valuationOf q 140 = false ∨ valuationOf q 273 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1044 (q : Snake 81) (h : Conditions q) : valuation q 140 = false ∨ valuation q 273 = true := counterClause1044 (baseVal q)

theorem counterClause1045 (q : Nat → Bool) : valuationOf q 140 = false ∨ valuationOf q 141 = false ∨ valuationOf q 274 = true := by
  have hs : count273 q = (countLit q [140]) + (countLit q [141]) := List.countP_append (p := literal q) (l₁ := [140]) (l₂ := [141])
  have hm := merge_two (literal (valuationOf q) (140)) (literal (valuationOf q) (141)) (literal (valuationOf q) (274)) (countLit q [140]) (countLit q [141]) (count273 q) 1 1 (meaning140 q) (meaning141 q) (meaning274 q) hs
  change valuationOf q 140 = false ∨ valuationOf q 141 = false ∨ valuationOf q 274 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1045 (q : Snake 81) (h : Conditions q) : valuation q 140 = false ∨ valuation q 141 = false ∨ valuation q 274 = true := counterClause1045 (baseVal q)

theorem counterClause1046 (q : Nat → Bool) : valuationOf q 143 = false ∨ valuationOf q 275 = true := by
  have hs : count275 q = (countLit q [142]) + (countLit q [143]) := List.countP_append (p := literal q) (l₁ := [142]) (l₂ := [143])
  have hm := merge_right (literal (valuationOf q) (143)) (literal (valuationOf q) (275)) (countLit q [142]) (countLit q [143]) (count275 q) 1 (meaning143 q) (meaning275 q) hs
  change valuationOf q 143 = false ∨ valuationOf q 275 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1046 (q : Snake 81) (h : Conditions q) : valuation q 143 = false ∨ valuation q 275 = true := counterClause1046 (baseVal q)

theorem counterClause1047 (q : Nat → Bool) : valuationOf q 275 = false ∨ valuationOf q 277 = true := by
  have hs : count277 q = (countLit q [140, 141]) + (countLit q [142, 143]) := List.countP_append (p := literal q) (l₁ := [140, 141]) (l₂ := [142, 143])
  have hm := merge_right (literal (valuationOf q) (275)) (literal (valuationOf q) (277)) (countLit q [140, 141]) (countLit q [142, 143]) (count277 q) 1 (meaning275 q) (meaning277 q) hs
  change valuationOf q 275 = false ∨ valuationOf q 277 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1047 (q : Snake 81) (h : Conditions q) : valuation q 275 = false ∨ valuation q 277 = true := counterClause1047 (baseVal q)

theorem counterClause1048 (q : Nat → Bool) : valuationOf q 273 = false ∨ valuationOf q 277 = true := by
  have hs : count277 q = (countLit q [140, 141]) + (countLit q [142, 143]) := List.countP_append (p := literal q) (l₁ := [140, 141]) (l₂ := [142, 143])
  have hm := merge_left (literal (valuationOf q) (273)) (literal (valuationOf q) (277)) (countLit q [140, 141]) (countLit q [142, 143]) (count277 q) 1 (meaning273 q) (meaning277 q) hs
  change valuationOf q 273 = false ∨ valuationOf q 277 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1048 (q : Snake 81) (h : Conditions q) : valuation q 273 = false ∨ valuation q 277 = true := counterClause1048 (baseVal q)

theorem counterClause1049 (q : Nat → Bool) : valuationOf q 273 = false ∨ valuationOf q 275 = false ∨ valuationOf q 278 = true := by
  have hs : count277 q = (countLit q [140, 141]) + (countLit q [142, 143]) := List.countP_append (p := literal q) (l₁ := [140, 141]) (l₂ := [142, 143])
  have hm := merge_two (literal (valuationOf q) (273)) (literal (valuationOf q) (275)) (literal (valuationOf q) (278)) (countLit q [140, 141]) (countLit q [142, 143]) (count277 q) 1 1 (meaning273 q) (meaning275 q) (meaning278 q) hs
  change valuationOf q 273 = false ∨ valuationOf q 275 = false ∨ valuationOf q 278 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1049 (q : Snake 81) (h : Conditions q) : valuation q 273 = false ∨ valuation q 275 = false ∨ valuation q 278 = true := counterClause1049 (baseVal q)

theorem counterClause1050 (q : Nat → Bool) : valuationOf q 274 = false ∨ valuationOf q 278 = true := by
  have hs : count277 q = (countLit q [140, 141]) + (countLit q [142, 143]) := List.countP_append (p := literal q) (l₁ := [140, 141]) (l₂ := [142, 143])
  have hm := merge_left (literal (valuationOf q) (274)) (literal (valuationOf q) (278)) (countLit q [140, 141]) (countLit q [142, 143]) (count277 q) 2 (meaning274 q) (meaning278 q) hs
  change valuationOf q 274 = false ∨ valuationOf q 278 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1050 (q : Snake 81) (h : Conditions q) : valuation q 274 = false ∨ valuation q 278 = true := counterClause1050 (baseVal q)

theorem counterClause1051 (q : Nat → Bool) : valuationOf q 277 = false ∨ valuationOf q 279 = true := by
  have hs : count279 q = (countLit q [136, 137, 138, 139]) + (countLit q [140, 141, 142, 143]) := List.countP_append (p := literal q) (l₁ := [136, 137, 138, 139]) (l₂ := [140, 141, 142, 143])
  have hm := merge_right (literal (valuationOf q) (277)) (literal (valuationOf q) (279)) (countLit q [136, 137, 138, 139]) (countLit q [140, 141, 142, 143]) (count279 q) 1 (meaning277 q) (meaning279 q) hs
  change valuationOf q 277 = false ∨ valuationOf q 279 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1051 (q : Snake 81) (h : Conditions q) : valuation q 277 = false ∨ valuation q 279 = true := counterClause1051 (baseVal q)

theorem counterClause1052 (q : Nat → Bool) : valuationOf q 278 = false ∨ valuationOf q 280 = true := by
  have hs : count279 q = (countLit q [136, 137, 138, 139]) + (countLit q [140, 141, 142, 143]) := List.countP_append (p := literal q) (l₁ := [136, 137, 138, 139]) (l₂ := [140, 141, 142, 143])
  have hm := merge_right (literal (valuationOf q) (278)) (literal (valuationOf q) (280)) (countLit q [136, 137, 138, 139]) (countLit q [140, 141, 142, 143]) (count279 q) 2 (meaning278 q) (meaning280 q) hs
  change valuationOf q 278 = false ∨ valuationOf q 280 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1052 (q : Snake 81) (h : Conditions q) : valuation q 278 = false ∨ valuation q 280 = true := counterClause1052 (baseVal q)

theorem counterClause1053 (q : Nat → Bool) : valuationOf q 271 = false ∨ valuationOf q 279 = true := by
  have hs : count279 q = (countLit q [136, 137, 138, 139]) + (countLit q [140, 141, 142, 143]) := List.countP_append (p := literal q) (l₁ := [136, 137, 138, 139]) (l₂ := [140, 141, 142, 143])
  have hm := merge_left (literal (valuationOf q) (271)) (literal (valuationOf q) (279)) (countLit q [136, 137, 138, 139]) (countLit q [140, 141, 142, 143]) (count279 q) 1 (meaning271 q) (meaning279 q) hs
  change valuationOf q 271 = false ∨ valuationOf q 279 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1053 (q : Snake 81) (h : Conditions q) : valuation q 271 = false ∨ valuation q 279 = true := counterClause1053 (baseVal q)

theorem counterClause1054 (q : Nat → Bool) : valuationOf q 271 = false ∨ valuationOf q 277 = false ∨ valuationOf q 280 = true := by
  have hs : count279 q = (countLit q [136, 137, 138, 139]) + (countLit q [140, 141, 142, 143]) := List.countP_append (p := literal q) (l₁ := [136, 137, 138, 139]) (l₂ := [140, 141, 142, 143])
  have hm := merge_two (literal (valuationOf q) (271)) (literal (valuationOf q) (277)) (literal (valuationOf q) (280)) (countLit q [136, 137, 138, 139]) (countLit q [140, 141, 142, 143]) (count279 q) 1 1 (meaning271 q) (meaning277 q) (meaning280 q) hs
  change valuationOf q 271 = false ∨ valuationOf q 277 = false ∨ valuationOf q 280 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1054 (q : Snake 81) (h : Conditions q) : valuation q 271 = false ∨ valuation q 277 = false ∨ valuation q 280 = true := counterClause1054 (baseVal q)

theorem counterClause1055 (q : Nat → Bool) : valuationOf q 279 = false ∨ valuationOf q 281 = true := by
  have hs : count281 q = (countLit q [129, 130, 131, 132, 133, 134, 135]) + (countLit q [136, 137, 138, 139, 140, 141, 142, 143]) := List.countP_append (p := literal q) (l₁ := [129, 130, 131, 132, 133, 134, 135]) (l₂ := [136, 137, 138, 139, 140, 141, 142, 143])
  have hm := merge_right (literal (valuationOf q) (279)) (literal (valuationOf q) (281)) (countLit q [129, 130, 131, 132, 133, 134, 135]) (countLit q [136, 137, 138, 139, 140, 141, 142, 143]) (count281 q) 1 (meaning279 q) (meaning281 q) hs
  change valuationOf q 279 = false ∨ valuationOf q 281 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1055 (q : Snake 81) (h : Conditions q) : valuation q 279 = false ∨ valuation q 281 = true := counterClause1055 (baseVal q)

theorem counterClause1056 (q : Nat → Bool) : valuationOf q 280 = false ∨ valuationOf q 282 = true := by
  have hs : count281 q = (countLit q [129, 130, 131, 132, 133, 134, 135]) + (countLit q [136, 137, 138, 139, 140, 141, 142, 143]) := List.countP_append (p := literal q) (l₁ := [129, 130, 131, 132, 133, 134, 135]) (l₂ := [136, 137, 138, 139, 140, 141, 142, 143])
  have hm := merge_right (literal (valuationOf q) (280)) (literal (valuationOf q) (282)) (countLit q [129, 130, 131, 132, 133, 134, 135]) (countLit q [136, 137, 138, 139, 140, 141, 142, 143]) (count281 q) 2 (meaning280 q) (meaning282 q) hs
  change valuationOf q 280 = false ∨ valuationOf q 282 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1056 (q : Snake 81) (h : Conditions q) : valuation q 280 = false ∨ valuation q 282 = true := counterClause1056 (baseVal q)

theorem block32 (q : Snake 81) (h : Conditions q) : B112E052.Block32 (valuation q) :=
  ⟨clause1025 q h, clause1026 q h, clause1027 q h, clause1028 q h, clause1029 q h, clause1030 q h, clause1031 q h, clause1032 q h, clause1033 q h, clause1034 q h, clause1035 q h, clause1036 q h, clause1037 q h, clause1038 q h, clause1039 q h, clause1040 q h, clause1041 q h, clause1042 q h, clause1043 q h, clause1044 q h, clause1045 q h, clause1046 q h, clause1047 q h, clause1048 q h, clause1049 q h, clause1050 q h, clause1051 q h, clause1052 q h, clause1053 q h, clause1054 q h, clause1055 q h, clause1056 q h⟩

end
end Snake9.Regrowth.E112052
