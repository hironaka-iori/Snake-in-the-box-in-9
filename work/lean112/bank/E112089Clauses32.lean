import E112089Semantics
import B112E089Inputs
namespace Snake9.Regrowth.E112089
noncomputable section
local instance blockDec32 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause1025 (q : Snake 81) (h : Conditions q) : valuation q 236 = false := by
  rw [value236]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (456 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause1026 (q : Snake 81) (h : Conditions q) : valuation q 238 = false := by
  rw [value238]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (462 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause1027 (q : Snake 81) (h : Conditions q) : valuation q 240 = false := by
  rw [value240]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (467 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause1028 (q : Snake 81) (h : Conditions q) : valuation q 242 = false := by
  rw [value242]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (469 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause1029 (q : Snake 81) (h : Conditions q) : valuation q 245 = false := by
  rw [value245]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (474 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause1030 (q : Snake 81) (h : Conditions q) : valuation q 248 = false := by
  rw [value248]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (479 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem counterClause1031 (q : Nat → Bool) : valuationOf q 126 = false ∨ valuationOf q 249 = true := by
  have hs : count249 q = (countLit q [126]) + (countLit q [127]) := List.countP_append (p := literal q) (l₁ := [126]) (l₂ := [127])
  have hm := merge_left (literal (valuationOf q) (126)) (literal (valuationOf q) (249)) (countLit q [126]) (countLit q [127]) (count249 q) 1 (meaning126 q) (meaning249 q) hs
  change valuationOf q 126 = false ∨ valuationOf q 249 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1031 (q : Snake 81) (h : Conditions q) : valuation q 126 = false ∨ valuation q 249 = true := counterClause1031 (baseVal q)

theorem counterClause1032 (q : Nat → Bool) : valuationOf q 249 = false ∨ valuationOf q 251 = true := by
  have hs : count251 q = (countLit q [125]) + (countLit q [126, 127]) := List.countP_append (p := literal q) (l₁ := [125]) (l₂ := [126, 127])
  have hm := merge_right (literal (valuationOf q) (249)) (literal (valuationOf q) (251)) (countLit q [125]) (countLit q [126, 127]) (count251 q) 1 (meaning249 q) (meaning251 q) hs
  change valuationOf q 249 = false ∨ valuationOf q 251 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1032 (q : Snake 81) (h : Conditions q) : valuation q 249 = false ∨ valuation q 251 = true := counterClause1032 (baseVal q)

theorem counterClause1033 (q : Nat → Bool) : valuationOf q 129 = false ∨ valuationOf q 253 = true := by
  have hs : count253 q = (countLit q [128]) + (countLit q [129]) := List.countP_append (p := literal q) (l₁ := [128]) (l₂ := [129])
  have hm := merge_right (literal (valuationOf q) (129)) (literal (valuationOf q) (253)) (countLit q [128]) (countLit q [129]) (count253 q) 1 (meaning129 q) (meaning253 q) hs
  change valuationOf q 129 = false ∨ valuationOf q 253 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1033 (q : Snake 81) (h : Conditions q) : valuation q 129 = false ∨ valuation q 253 = true := counterClause1033 (baseVal q)

theorem counterClause1034 (q : Nat → Bool) : valuationOf q 253 = false ∨ valuationOf q 257 = true := by
  have hs : count257 q = (countLit q [128, 129]) + (countLit q [130, 131]) := List.countP_append (p := literal q) (l₁ := [128, 129]) (l₂ := [130, 131])
  have hm := merge_left (literal (valuationOf q) (253)) (literal (valuationOf q) (257)) (countLit q [128, 129]) (countLit q [130, 131]) (count257 q) 1 (meaning253 q) (meaning257 q) hs
  change valuationOf q 253 = false ∨ valuationOf q 257 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1034 (q : Snake 81) (h : Conditions q) : valuation q 253 = false ∨ valuation q 257 = true := counterClause1034 (baseVal q)

theorem counterClause1035 (q : Nat → Bool) : valuationOf q 257 = false ∨ valuationOf q 259 = true := by
  have hs : count259 q = (countLit q [125, 126, 127]) + (countLit q [128, 129, 130, 131]) := List.countP_append (p := literal q) (l₁ := [125, 126, 127]) (l₂ := [128, 129, 130, 131])
  have hm := merge_right (literal (valuationOf q) (257)) (literal (valuationOf q) (259)) (countLit q [125, 126, 127]) (countLit q [128, 129, 130, 131]) (count259 q) 1 (meaning257 q) (meaning259 q) hs
  change valuationOf q 257 = false ∨ valuationOf q 259 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1035 (q : Snake 81) (h : Conditions q) : valuation q 257 = false ∨ valuation q 259 = true := counterClause1035 (baseVal q)

theorem counterClause1036 (q : Nat → Bool) : valuationOf q 251 = false ∨ valuationOf q 259 = true := by
  have hs : count259 q = (countLit q [125, 126, 127]) + (countLit q [128, 129, 130, 131]) := List.countP_append (p := literal q) (l₁ := [125, 126, 127]) (l₂ := [128, 129, 130, 131])
  have hm := merge_left (literal (valuationOf q) (251)) (literal (valuationOf q) (259)) (countLit q [125, 126, 127]) (countLit q [128, 129, 130, 131]) (count259 q) 1 (meaning251 q) (meaning259 q) hs
  change valuationOf q 251 = false ∨ valuationOf q 259 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1036 (q : Snake 81) (h : Conditions q) : valuation q 251 = false ∨ valuation q 259 = true := counterClause1036 (baseVal q)

theorem counterClause1037 (q : Nat → Bool) : valuationOf q 133 = false ∨ valuationOf q 261 = true := by
  have hs : count261 q = (countLit q [132]) + (countLit q [133]) := List.countP_append (p := literal q) (l₁ := [132]) (l₂ := [133])
  have hm := merge_right (literal (valuationOf q) (133)) (literal (valuationOf q) (261)) (countLit q [132]) (countLit q [133]) (count261 q) 1 (meaning133 q) (meaning261 q) hs
  change valuationOf q 133 = false ∨ valuationOf q 261 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1037 (q : Snake 81) (h : Conditions q) : valuation q 133 = false ∨ valuation q 261 = true := counterClause1037 (baseVal q)

theorem counterClause1038 (q : Nat → Bool) : valuationOf q 132 = false ∨ valuationOf q 261 = true := by
  have hs : count261 q = (countLit q [132]) + (countLit q [133]) := List.countP_append (p := literal q) (l₁ := [132]) (l₂ := [133])
  have hm := merge_left (literal (valuationOf q) (132)) (literal (valuationOf q) (261)) (countLit q [132]) (countLit q [133]) (count261 q) 1 (meaning132 q) (meaning261 q) hs
  change valuationOf q 132 = false ∨ valuationOf q 261 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1038 (q : Snake 81) (h : Conditions q) : valuation q 132 = false ∨ valuation q 261 = true := counterClause1038 (baseVal q)

theorem counterClause1039 (q : Nat → Bool) : valuationOf q 132 = false ∨ valuationOf q 133 = false ∨ valuationOf q 262 = true := by
  have hs : count261 q = (countLit q [132]) + (countLit q [133]) := List.countP_append (p := literal q) (l₁ := [132]) (l₂ := [133])
  have hm := merge_two (literal (valuationOf q) (132)) (literal (valuationOf q) (133)) (literal (valuationOf q) (262)) (countLit q [132]) (countLit q [133]) (count261 q) 1 1 (meaning132 q) (meaning133 q) (meaning262 q) hs
  change valuationOf q 132 = false ∨ valuationOf q 133 = false ∨ valuationOf q 262 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1039 (q : Snake 81) (h : Conditions q) : valuation q 132 = false ∨ valuation q 133 = false ∨ valuation q 262 = true := counterClause1039 (baseVal q)

theorem counterClause1040 (q : Nat → Bool) : valuationOf q 135 = false ∨ valuationOf q 263 = true := by
  have hs : count263 q = (countLit q [134]) + (countLit q [135]) := List.countP_append (p := literal q) (l₁ := [134]) (l₂ := [135])
  have hm := merge_right (literal (valuationOf q) (135)) (literal (valuationOf q) (263)) (countLit q [134]) (countLit q [135]) (count263 q) 1 (meaning135 q) (meaning263 q) hs
  change valuationOf q 135 = false ∨ valuationOf q 263 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1040 (q : Snake 81) (h : Conditions q) : valuation q 135 = false ∨ valuation q 263 = true := counterClause1040 (baseVal q)

theorem counterClause1041 (q : Nat → Bool) : valuationOf q 134 = false ∨ valuationOf q 263 = true := by
  have hs : count263 q = (countLit q [134]) + (countLit q [135]) := List.countP_append (p := literal q) (l₁ := [134]) (l₂ := [135])
  have hm := merge_left (literal (valuationOf q) (134)) (literal (valuationOf q) (263)) (countLit q [134]) (countLit q [135]) (count263 q) 1 (meaning134 q) (meaning263 q) hs
  change valuationOf q 134 = false ∨ valuationOf q 263 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1041 (q : Snake 81) (h : Conditions q) : valuation q 134 = false ∨ valuation q 263 = true := counterClause1041 (baseVal q)

theorem counterClause1042 (q : Nat → Bool) : valuationOf q 134 = false ∨ valuationOf q 135 = false ∨ valuationOf q 264 = true := by
  have hs : count263 q = (countLit q [134]) + (countLit q [135]) := List.countP_append (p := literal q) (l₁ := [134]) (l₂ := [135])
  have hm := merge_two (literal (valuationOf q) (134)) (literal (valuationOf q) (135)) (literal (valuationOf q) (264)) (countLit q [134]) (countLit q [135]) (count263 q) 1 1 (meaning134 q) (meaning135 q) (meaning264 q) hs
  change valuationOf q 134 = false ∨ valuationOf q 135 = false ∨ valuationOf q 264 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1042 (q : Snake 81) (h : Conditions q) : valuation q 134 = false ∨ valuation q 135 = false ∨ valuation q 264 = true := counterClause1042 (baseVal q)

theorem counterClause1043 (q : Nat → Bool) : valuationOf q 263 = false ∨ valuationOf q 265 = true := by
  have hs : count265 q = (countLit q [132, 133]) + (countLit q [134, 135]) := List.countP_append (p := literal q) (l₁ := [132, 133]) (l₂ := [134, 135])
  have hm := merge_right (literal (valuationOf q) (263)) (literal (valuationOf q) (265)) (countLit q [132, 133]) (countLit q [134, 135]) (count265 q) 1 (meaning263 q) (meaning265 q) hs
  change valuationOf q 263 = false ∨ valuationOf q 265 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1043 (q : Snake 81) (h : Conditions q) : valuation q 263 = false ∨ valuation q 265 = true := counterClause1043 (baseVal q)

theorem counterClause1044 (q : Nat → Bool) : valuationOf q 264 = false ∨ valuationOf q 266 = true := by
  have hs : count265 q = (countLit q [132, 133]) + (countLit q [134, 135]) := List.countP_append (p := literal q) (l₁ := [132, 133]) (l₂ := [134, 135])
  have hm := merge_right (literal (valuationOf q) (264)) (literal (valuationOf q) (266)) (countLit q [132, 133]) (countLit q [134, 135]) (count265 q) 2 (meaning264 q) (meaning266 q) hs
  change valuationOf q 264 = false ∨ valuationOf q 266 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1044 (q : Snake 81) (h : Conditions q) : valuation q 264 = false ∨ valuation q 266 = true := counterClause1044 (baseVal q)

theorem counterClause1045 (q : Nat → Bool) : valuationOf q 261 = false ∨ valuationOf q 265 = true := by
  have hs : count265 q = (countLit q [132, 133]) + (countLit q [134, 135]) := List.countP_append (p := literal q) (l₁ := [132, 133]) (l₂ := [134, 135])
  have hm := merge_left (literal (valuationOf q) (261)) (literal (valuationOf q) (265)) (countLit q [132, 133]) (countLit q [134, 135]) (count265 q) 1 (meaning261 q) (meaning265 q) hs
  change valuationOf q 261 = false ∨ valuationOf q 265 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1045 (q : Snake 81) (h : Conditions q) : valuation q 261 = false ∨ valuation q 265 = true := counterClause1045 (baseVal q)

theorem counterClause1046 (q : Nat → Bool) : valuationOf q 261 = false ∨ valuationOf q 263 = false ∨ valuationOf q 266 = true := by
  have hs : count265 q = (countLit q [132, 133]) + (countLit q [134, 135]) := List.countP_append (p := literal q) (l₁ := [132, 133]) (l₂ := [134, 135])
  have hm := merge_two (literal (valuationOf q) (261)) (literal (valuationOf q) (263)) (literal (valuationOf q) (266)) (countLit q [132, 133]) (countLit q [134, 135]) (count265 q) 1 1 (meaning261 q) (meaning263 q) (meaning266 q) hs
  change valuationOf q 261 = false ∨ valuationOf q 263 = false ∨ valuationOf q 266 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1046 (q : Snake 81) (h : Conditions q) : valuation q 261 = false ∨ valuation q 263 = false ∨ valuation q 266 = true := counterClause1046 (baseVal q)

theorem counterClause1047 (q : Nat → Bool) : valuationOf q 262 = false ∨ valuationOf q 266 = true := by
  have hs : count265 q = (countLit q [132, 133]) + (countLit q [134, 135]) := List.countP_append (p := literal q) (l₁ := [132, 133]) (l₂ := [134, 135])
  have hm := merge_left (literal (valuationOf q) (262)) (literal (valuationOf q) (266)) (countLit q [132, 133]) (countLit q [134, 135]) (count265 q) 2 (meaning262 q) (meaning266 q) hs
  change valuationOf q 262 = false ∨ valuationOf q 266 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1047 (q : Snake 81) (h : Conditions q) : valuation q 262 = false ∨ valuation q 266 = true := counterClause1047 (baseVal q)

theorem counterClause1048 (q : Nat → Bool) : valuationOf q 137 = false ∨ valuationOf q 267 = true := by
  have hs : count267 q = (countLit q [136]) + (countLit q [137]) := List.countP_append (p := literal q) (l₁ := [136]) (l₂ := [137])
  have hm := merge_right (literal (valuationOf q) (137)) (literal (valuationOf q) (267)) (countLit q [136]) (countLit q [137]) (count267 q) 1 (meaning137 q) (meaning267 q) hs
  change valuationOf q 137 = false ∨ valuationOf q 267 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1048 (q : Snake 81) (h : Conditions q) : valuation q 137 = false ∨ valuation q 267 = true := counterClause1048 (baseVal q)

theorem counterClause1049 (q : Nat → Bool) : valuationOf q 139 = false ∨ valuationOf q 269 = true := by
  have hs : count269 q = (countLit q [138]) + (countLit q [139]) := List.countP_append (p := literal q) (l₁ := [138]) (l₂ := [139])
  have hm := merge_right (literal (valuationOf q) (139)) (literal (valuationOf q) (269)) (countLit q [138]) (countLit q [139]) (count269 q) 1 (meaning139 q) (meaning269 q) hs
  change valuationOf q 139 = false ∨ valuationOf q 269 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1049 (q : Snake 81) (h : Conditions q) : valuation q 139 = false ∨ valuation q 269 = true := counterClause1049 (baseVal q)

theorem counterClause1050 (q : Nat → Bool) : valuationOf q 138 = false ∨ valuationOf q 269 = true := by
  have hs : count269 q = (countLit q [138]) + (countLit q [139]) := List.countP_append (p := literal q) (l₁ := [138]) (l₂ := [139])
  have hm := merge_left (literal (valuationOf q) (138)) (literal (valuationOf q) (269)) (countLit q [138]) (countLit q [139]) (count269 q) 1 (meaning138 q) (meaning269 q) hs
  change valuationOf q 138 = false ∨ valuationOf q 269 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1050 (q : Snake 81) (h : Conditions q) : valuation q 138 = false ∨ valuation q 269 = true := counterClause1050 (baseVal q)

theorem counterClause1051 (q : Nat → Bool) : valuationOf q 138 = false ∨ valuationOf q 139 = false ∨ valuationOf q 270 = true := by
  have hs : count269 q = (countLit q [138]) + (countLit q [139]) := List.countP_append (p := literal q) (l₁ := [138]) (l₂ := [139])
  have hm := merge_two (literal (valuationOf q) (138)) (literal (valuationOf q) (139)) (literal (valuationOf q) (270)) (countLit q [138]) (countLit q [139]) (count269 q) 1 1 (meaning138 q) (meaning139 q) (meaning270 q) hs
  change valuationOf q 138 = false ∨ valuationOf q 139 = false ∨ valuationOf q 270 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1051 (q : Snake 81) (h : Conditions q) : valuation q 138 = false ∨ valuation q 139 = false ∨ valuation q 270 = true := counterClause1051 (baseVal q)

theorem counterClause1052 (q : Nat → Bool) : valuationOf q 269 = false ∨ valuationOf q 271 = true := by
  have hs : count271 q = (countLit q [136, 137]) + (countLit q [138, 139]) := List.countP_append (p := literal q) (l₁ := [136, 137]) (l₂ := [138, 139])
  have hm := merge_right (literal (valuationOf q) (269)) (literal (valuationOf q) (271)) (countLit q [136, 137]) (countLit q [138, 139]) (count271 q) 1 (meaning269 q) (meaning271 q) hs
  change valuationOf q 269 = false ∨ valuationOf q 271 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1052 (q : Snake 81) (h : Conditions q) : valuation q 269 = false ∨ valuation q 271 = true := counterClause1052 (baseVal q)

theorem counterClause1053 (q : Nat → Bool) : valuationOf q 270 = false ∨ valuationOf q 272 = true := by
  have hs : count271 q = (countLit q [136, 137]) + (countLit q [138, 139]) := List.countP_append (p := literal q) (l₁ := [136, 137]) (l₂ := [138, 139])
  have hm := merge_right (literal (valuationOf q) (270)) (literal (valuationOf q) (272)) (countLit q [136, 137]) (countLit q [138, 139]) (count271 q) 2 (meaning270 q) (meaning272 q) hs
  change valuationOf q 270 = false ∨ valuationOf q 272 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1053 (q : Snake 81) (h : Conditions q) : valuation q 270 = false ∨ valuation q 272 = true := counterClause1053 (baseVal q)

theorem counterClause1054 (q : Nat → Bool) : valuationOf q 267 = false ∨ valuationOf q 271 = true := by
  have hs : count271 q = (countLit q [136, 137]) + (countLit q [138, 139]) := List.countP_append (p := literal q) (l₁ := [136, 137]) (l₂ := [138, 139])
  have hm := merge_left (literal (valuationOf q) (267)) (literal (valuationOf q) (271)) (countLit q [136, 137]) (countLit q [138, 139]) (count271 q) 1 (meaning267 q) (meaning271 q) hs
  change valuationOf q 267 = false ∨ valuationOf q 271 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1054 (q : Snake 81) (h : Conditions q) : valuation q 267 = false ∨ valuation q 271 = true := counterClause1054 (baseVal q)

theorem counterClause1055 (q : Nat → Bool) : valuationOf q 267 = false ∨ valuationOf q 269 = false ∨ valuationOf q 272 = true := by
  have hs : count271 q = (countLit q [136, 137]) + (countLit q [138, 139]) := List.countP_append (p := literal q) (l₁ := [136, 137]) (l₂ := [138, 139])
  have hm := merge_two (literal (valuationOf q) (267)) (literal (valuationOf q) (269)) (literal (valuationOf q) (272)) (countLit q [136, 137]) (countLit q [138, 139]) (count271 q) 1 1 (meaning267 q) (meaning269 q) (meaning272 q) hs
  change valuationOf q 267 = false ∨ valuationOf q 269 = false ∨ valuationOf q 272 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1055 (q : Snake 81) (h : Conditions q) : valuation q 267 = false ∨ valuation q 269 = false ∨ valuation q 272 = true := counterClause1055 (baseVal q)

theorem counterClause1056 (q : Nat → Bool) : valuationOf q 271 = false ∨ valuationOf q 273 = true := by
  have hs : count273 q = (countLit q [132, 133, 134, 135]) + (countLit q [136, 137, 138, 139]) := List.countP_append (p := literal q) (l₁ := [132, 133, 134, 135]) (l₂ := [136, 137, 138, 139])
  have hm := merge_right (literal (valuationOf q) (271)) (literal (valuationOf q) (273)) (countLit q [132, 133, 134, 135]) (countLit q [136, 137, 138, 139]) (count273 q) 1 (meaning271 q) (meaning273 q) hs
  change valuationOf q 271 = false ∨ valuationOf q 273 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1056 (q : Snake 81) (h : Conditions q) : valuation q 271 = false ∨ valuation q 273 = true := counterClause1056 (baseVal q)

theorem block32 (q : Snake 81) (h : Conditions q) : B112E089.Block32 (valuation q) :=
  ⟨clause1025 q h, clause1026 q h, clause1027 q h, clause1028 q h, clause1029 q h, clause1030 q h, clause1031 q h, clause1032 q h, clause1033 q h, clause1034 q h, clause1035 q h, clause1036 q h, clause1037 q h, clause1038 q h, clause1039 q h, clause1040 q h, clause1041 q h, clause1042 q h, clause1043 q h, clause1044 q h, clause1045 q h, clause1046 q h, clause1047 q h, clause1048 q h, clause1049 q h, clause1050 q h, clause1051 q h, clause1052 q h, clause1053 q h, clause1054 q h, clause1055 q h, clause1056 q h⟩

end
end Snake9.Regrowth.E112089
