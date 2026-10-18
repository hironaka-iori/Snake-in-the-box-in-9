import E112121Semantics
import B112E121Inputs
namespace Snake9.Regrowth.E112121
noncomputable section
local instance blockDec29 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause929 (q : Snake 81) (h : Conditions q) : valuation q 236 = false := by
  rw [value236]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (480 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause930 (q : Snake 81) (h : Conditions q) : valuation q 238 = false := by
  rw [value238]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (486 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause931 (q : Snake 81) (h : Conditions q) : valuation q 244 = false := by
  rw [value244]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (495 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause932 (q : Snake 81) (h : Conditions q) : valuation q 245 = false := by
  rw [value245]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (497 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause933 (q : Snake 81) (h : Conditions q) : valuation q 246 = false := by
  rw [value246]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (498 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause934 (q : Snake 81) (h : Conditions q) : valuation q 251 = false := by
  rw [value251]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (509 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem counterClause935 (q : Nat → Bool) : valuationOf q 128 = false ∨ valuationOf q 253 = true := by
  have hs : count253 q = (countLit q [128]) + (countLit q [129]) := List.countP_append (p := literal q) (l₁ := [128]) (l₂ := [129])
  have hm := merge_left (literal (valuationOf q) (128)) (literal (valuationOf q) (253)) (countLit q [128]) (countLit q [129]) (count253 q) 1 (meaning128 q) (meaning253 q) hs
  change valuationOf q 128 = false ∨ valuationOf q 253 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause935 (q : Snake 81) (h : Conditions q) : valuation q 128 = false ∨ valuation q 253 = true := counterClause935 (baseVal q)

theorem counterClause936 (q : Nat → Bool) : valuationOf q 253 = false ∨ valuationOf q 255 = true := by
  have hs : count255 q = (countLit q [127]) + (countLit q [128, 129]) := List.countP_append (p := literal q) (l₁ := [127]) (l₂ := [128, 129])
  have hm := merge_right (literal (valuationOf q) (253)) (literal (valuationOf q) (255)) (countLit q [127]) (countLit q [128, 129]) (count255 q) 1 (meaning253 q) (meaning255 q) hs
  change valuationOf q 253 = false ∨ valuationOf q 255 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause936 (q : Snake 81) (h : Conditions q) : valuation q 253 = false ∨ valuation q 255 = true := counterClause936 (baseVal q)

theorem counterClause937 (q : Nat → Bool) : valuationOf q 133 = false ∨ valuationOf q 259 = true := by
  have hs : count259 q = (countLit q [132]) + (countLit q [133]) := List.countP_append (p := literal q) (l₁ := [132]) (l₂ := [133])
  have hm := merge_right (literal (valuationOf q) (133)) (literal (valuationOf q) (259)) (countLit q [132]) (countLit q [133]) (count259 q) 1 (meaning133 q) (meaning259 q) hs
  change valuationOf q 133 = false ∨ valuationOf q 259 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause937 (q : Snake 81) (h : Conditions q) : valuation q 133 = false ∨ valuation q 259 = true := counterClause937 (baseVal q)

theorem counterClause938 (q : Nat → Bool) : valuationOf q 132 = false ∨ valuationOf q 259 = true := by
  have hs : count259 q = (countLit q [132]) + (countLit q [133]) := List.countP_append (p := literal q) (l₁ := [132]) (l₂ := [133])
  have hm := merge_left (literal (valuationOf q) (132)) (literal (valuationOf q) (259)) (countLit q [132]) (countLit q [133]) (count259 q) 1 (meaning132 q) (meaning259 q) hs
  change valuationOf q 132 = false ∨ valuationOf q 259 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause938 (q : Snake 81) (h : Conditions q) : valuation q 132 = false ∨ valuation q 259 = true := counterClause938 (baseVal q)

theorem counterClause939 (q : Nat → Bool) : valuationOf q 132 = false ∨ valuationOf q 133 = false ∨ valuationOf q 260 = true := by
  have hs : count259 q = (countLit q [132]) + (countLit q [133]) := List.countP_append (p := literal q) (l₁ := [132]) (l₂ := [133])
  have hm := merge_two (literal (valuationOf q) (132)) (literal (valuationOf q) (133)) (literal (valuationOf q) (260)) (countLit q [132]) (countLit q [133]) (count259 q) 1 1 (meaning132 q) (meaning133 q) (meaning260 q) hs
  change valuationOf q 132 = false ∨ valuationOf q 133 = false ∨ valuationOf q 260 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause939 (q : Snake 81) (h : Conditions q) : valuation q 132 = false ∨ valuation q 133 = false ∨ valuation q 260 = true := counterClause939 (baseVal q)

theorem counterClause940 (q : Nat → Bool) : valuationOf q 259 = false ∨ valuationOf q 261 = true := by
  have hs : count261 q = (countLit q [130, 131]) + (countLit q [132, 133]) := List.countP_append (p := literal q) (l₁ := [130, 131]) (l₂ := [132, 133])
  have hm := merge_right (literal (valuationOf q) (259)) (literal (valuationOf q) (261)) (countLit q [130, 131]) (countLit q [132, 133]) (count261 q) 1 (meaning259 q) (meaning261 q) hs
  change valuationOf q 259 = false ∨ valuationOf q 261 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause940 (q : Snake 81) (h : Conditions q) : valuation q 259 = false ∨ valuation q 261 = true := counterClause940 (baseVal q)

theorem counterClause941 (q : Nat → Bool) : valuationOf q 260 = false ∨ valuationOf q 262 = true := by
  have hs : count261 q = (countLit q [130, 131]) + (countLit q [132, 133]) := List.countP_append (p := literal q) (l₁ := [130, 131]) (l₂ := [132, 133])
  have hm := merge_right (literal (valuationOf q) (260)) (literal (valuationOf q) (262)) (countLit q [130, 131]) (countLit q [132, 133]) (count261 q) 2 (meaning260 q) (meaning262 q) hs
  change valuationOf q 260 = false ∨ valuationOf q 262 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause941 (q : Snake 81) (h : Conditions q) : valuation q 260 = false ∨ valuation q 262 = true := counterClause941 (baseVal q)

theorem counterClause942 (q : Nat → Bool) : valuationOf q 261 = false ∨ valuationOf q 263 = true := by
  have hs : count263 q = (countLit q [127, 128, 129]) + (countLit q [130, 131, 132, 133]) := List.countP_append (p := literal q) (l₁ := [127, 128, 129]) (l₂ := [130, 131, 132, 133])
  have hm := merge_right (literal (valuationOf q) (261)) (literal (valuationOf q) (263)) (countLit q [127, 128, 129]) (countLit q [130, 131, 132, 133]) (count263 q) 1 (meaning261 q) (meaning263 q) hs
  change valuationOf q 261 = false ∨ valuationOf q 263 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause942 (q : Snake 81) (h : Conditions q) : valuation q 261 = false ∨ valuation q 263 = true := counterClause942 (baseVal q)

theorem counterClause943 (q : Nat → Bool) : valuationOf q 262 = false ∨ valuationOf q 264 = true := by
  have hs : count263 q = (countLit q [127, 128, 129]) + (countLit q [130, 131, 132, 133]) := List.countP_append (p := literal q) (l₁ := [127, 128, 129]) (l₂ := [130, 131, 132, 133])
  have hm := merge_right (literal (valuationOf q) (262)) (literal (valuationOf q) (264)) (countLit q [127, 128, 129]) (countLit q [130, 131, 132, 133]) (count263 q) 2 (meaning262 q) (meaning264 q) hs
  change valuationOf q 262 = false ∨ valuationOf q 264 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause943 (q : Snake 81) (h : Conditions q) : valuation q 262 = false ∨ valuation q 264 = true := counterClause943 (baseVal q)

theorem counterClause944 (q : Nat → Bool) : valuationOf q 255 = false ∨ valuationOf q 263 = true := by
  have hs : count263 q = (countLit q [127, 128, 129]) + (countLit q [130, 131, 132, 133]) := List.countP_append (p := literal q) (l₁ := [127, 128, 129]) (l₂ := [130, 131, 132, 133])
  have hm := merge_left (literal (valuationOf q) (255)) (literal (valuationOf q) (263)) (countLit q [127, 128, 129]) (countLit q [130, 131, 132, 133]) (count263 q) 1 (meaning255 q) (meaning263 q) hs
  change valuationOf q 255 = false ∨ valuationOf q 263 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause944 (q : Snake 81) (h : Conditions q) : valuation q 255 = false ∨ valuation q 263 = true := counterClause944 (baseVal q)

theorem counterClause945 (q : Nat → Bool) : valuationOf q 255 = false ∨ valuationOf q 261 = false ∨ valuationOf q 264 = true := by
  have hs : count263 q = (countLit q [127, 128, 129]) + (countLit q [130, 131, 132, 133]) := List.countP_append (p := literal q) (l₁ := [127, 128, 129]) (l₂ := [130, 131, 132, 133])
  have hm := merge_two (literal (valuationOf q) (255)) (literal (valuationOf q) (261)) (literal (valuationOf q) (264)) (countLit q [127, 128, 129]) (countLit q [130, 131, 132, 133]) (count263 q) 1 1 (meaning255 q) (meaning261 q) (meaning264 q) hs
  change valuationOf q 255 = false ∨ valuationOf q 261 = false ∨ valuationOf q 264 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause945 (q : Snake 81) (h : Conditions q) : valuation q 255 = false ∨ valuation q 261 = false ∨ valuation q 264 = true := counterClause945 (baseVal q)

theorem counterClause946 (q : Nat → Bool) : valuationOf q 134 = false ∨ valuationOf q 265 = true := by
  have hs : count265 q = (countLit q [134]) + (countLit q [135]) := List.countP_append (p := literal q) (l₁ := [134]) (l₂ := [135])
  have hm := merge_left (literal (valuationOf q) (134)) (literal (valuationOf q) (265)) (countLit q [134]) (countLit q [135]) (count265 q) 1 (meaning134 q) (meaning265 q) hs
  change valuationOf q 134 = false ∨ valuationOf q 265 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause946 (q : Snake 81) (h : Conditions q) : valuation q 134 = false ∨ valuation q 265 = true := counterClause946 (baseVal q)

theorem counterClause947 (q : Nat → Bool) : valuationOf q 265 = false ∨ valuationOf q 269 = true := by
  have hs : count269 q = (countLit q [134, 135]) + (countLit q [136, 137]) := List.countP_append (p := literal q) (l₁ := [134, 135]) (l₂ := [136, 137])
  have hm := merge_left (literal (valuationOf q) (265)) (literal (valuationOf q) (269)) (countLit q [134, 135]) (countLit q [136, 137]) (count269 q) 1 (meaning265 q) (meaning269 q) hs
  change valuationOf q 265 = false ∨ valuationOf q 269 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause947 (q : Snake 81) (h : Conditions q) : valuation q 265 = false ∨ valuation q 269 = true := counterClause947 (baseVal q)

theorem counterClause948 (q : Nat → Bool) : valuationOf q 138 = false ∨ valuationOf q 271 = true := by
  have hs : count271 q = (countLit q [138]) + (countLit q [139]) := List.countP_append (p := literal q) (l₁ := [138]) (l₂ := [139])
  have hm := merge_left (literal (valuationOf q) (138)) (literal (valuationOf q) (271)) (countLit q [138]) (countLit q [139]) (count271 q) 1 (meaning138 q) (meaning271 q) hs
  change valuationOf q 138 = false ∨ valuationOf q 271 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause948 (q : Snake 81) (h : Conditions q) : valuation q 138 = false ∨ valuation q 271 = true := counterClause948 (baseVal q)

theorem counterClause949 (q : Nat → Bool) : valuationOf q 271 = false ∨ valuationOf q 275 = true := by
  have hs : count275 q = (countLit q [138, 139]) + (countLit q [140, 141]) := List.countP_append (p := literal q) (l₁ := [138, 139]) (l₂ := [140, 141])
  have hm := merge_left (literal (valuationOf q) (271)) (literal (valuationOf q) (275)) (countLit q [138, 139]) (countLit q [140, 141]) (count275 q) 1 (meaning271 q) (meaning275 q) hs
  change valuationOf q 271 = false ∨ valuationOf q 275 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause949 (q : Snake 81) (h : Conditions q) : valuation q 271 = false ∨ valuation q 275 = true := counterClause949 (baseVal q)

theorem counterClause950 (q : Nat → Bool) : valuationOf q 275 = false ∨ valuationOf q 277 = true := by
  have hs : count277 q = (countLit q [134, 135, 136, 137]) + (countLit q [138, 139, 140, 141]) := List.countP_append (p := literal q) (l₁ := [134, 135, 136, 137]) (l₂ := [138, 139, 140, 141])
  have hm := merge_right (literal (valuationOf q) (275)) (literal (valuationOf q) (277)) (countLit q [134, 135, 136, 137]) (countLit q [138, 139, 140, 141]) (count277 q) 1 (meaning275 q) (meaning277 q) hs
  change valuationOf q 275 = false ∨ valuationOf q 277 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause950 (q : Snake 81) (h : Conditions q) : valuation q 275 = false ∨ valuation q 277 = true := counterClause950 (baseVal q)

theorem counterClause951 (q : Nat → Bool) : valuationOf q 269 = false ∨ valuationOf q 277 = true := by
  have hs : count277 q = (countLit q [134, 135, 136, 137]) + (countLit q [138, 139, 140, 141]) := List.countP_append (p := literal q) (l₁ := [134, 135, 136, 137]) (l₂ := [138, 139, 140, 141])
  have hm := merge_left (literal (valuationOf q) (269)) (literal (valuationOf q) (277)) (countLit q [134, 135, 136, 137]) (countLit q [138, 139, 140, 141]) (count277 q) 1 (meaning269 q) (meaning277 q) hs
  change valuationOf q 269 = false ∨ valuationOf q 277 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause951 (q : Snake 81) (h : Conditions q) : valuation q 269 = false ∨ valuation q 277 = true := counterClause951 (baseVal q)

theorem counterClause952 (q : Nat → Bool) : valuationOf q 277 = false ∨ valuationOf q 279 = true := by
  have hs : count279 q = (countLit q [127, 128, 129, 130, 131, 132, 133]) + (countLit q [134, 135, 136, 137, 138, 139, 140, 141]) := List.countP_append (p := literal q) (l₁ := [127, 128, 129, 130, 131, 132, 133]) (l₂ := [134, 135, 136, 137, 138, 139, 140, 141])
  have hm := merge_right (literal (valuationOf q) (277)) (literal (valuationOf q) (279)) (countLit q [127, 128, 129, 130, 131, 132, 133]) (countLit q [134, 135, 136, 137, 138, 139, 140, 141]) (count279 q) 1 (meaning277 q) (meaning279 q) hs
  change valuationOf q 277 = false ∨ valuationOf q 279 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause952 (q : Snake 81) (h : Conditions q) : valuation q 277 = false ∨ valuation q 279 = true := counterClause952 (baseVal q)

theorem counterClause953 (q : Nat → Bool) : valuationOf q 263 = false ∨ valuationOf q 279 = true := by
  have hs : count279 q = (countLit q [127, 128, 129, 130, 131, 132, 133]) + (countLit q [134, 135, 136, 137, 138, 139, 140, 141]) := List.countP_append (p := literal q) (l₁ := [127, 128, 129, 130, 131, 132, 133]) (l₂ := [134, 135, 136, 137, 138, 139, 140, 141])
  have hm := merge_left (literal (valuationOf q) (263)) (literal (valuationOf q) (279)) (countLit q [127, 128, 129, 130, 131, 132, 133]) (countLit q [134, 135, 136, 137, 138, 139, 140, 141]) (count279 q) 1 (meaning263 q) (meaning279 q) hs
  change valuationOf q 263 = false ∨ valuationOf q 279 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause953 (q : Snake 81) (h : Conditions q) : valuation q 263 = false ∨ valuation q 279 = true := counterClause953 (baseVal q)

theorem counterClause954 (q : Nat → Bool) : valuationOf q 263 = false ∨ valuationOf q 277 = false ∨ valuationOf q 280 = true := by
  have hs : count279 q = (countLit q [127, 128, 129, 130, 131, 132, 133]) + (countLit q [134, 135, 136, 137, 138, 139, 140, 141]) := List.countP_append (p := literal q) (l₁ := [127, 128, 129, 130, 131, 132, 133]) (l₂ := [134, 135, 136, 137, 138, 139, 140, 141])
  have hm := merge_two (literal (valuationOf q) (263)) (literal (valuationOf q) (277)) (literal (valuationOf q) (280)) (countLit q [127, 128, 129, 130, 131, 132, 133]) (countLit q [134, 135, 136, 137, 138, 139, 140, 141]) (count279 q) 1 1 (meaning263 q) (meaning277 q) (meaning280 q) hs
  change valuationOf q 263 = false ∨ valuationOf q 277 = false ∨ valuationOf q 280 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause954 (q : Snake 81) (h : Conditions q) : valuation q 263 = false ∨ valuation q 277 = false ∨ valuation q 280 = true := counterClause954 (baseVal q)

theorem counterClause955 (q : Nat → Bool) : valuationOf q 264 = false ∨ valuationOf q 280 = true := by
  have hs : count279 q = (countLit q [127, 128, 129, 130, 131, 132, 133]) + (countLit q [134, 135, 136, 137, 138, 139, 140, 141]) := List.countP_append (p := literal q) (l₁ := [127, 128, 129, 130, 131, 132, 133]) (l₂ := [134, 135, 136, 137, 138, 139, 140, 141])
  have hm := merge_left (literal (valuationOf q) (264)) (literal (valuationOf q) (280)) (countLit q [127, 128, 129, 130, 131, 132, 133]) (countLit q [134, 135, 136, 137, 138, 139, 140, 141]) (count279 q) 2 (meaning264 q) (meaning280 q) hs
  change valuationOf q 264 = false ∨ valuationOf q 280 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause955 (q : Snake 81) (h : Conditions q) : valuation q 264 = false ∨ valuation q 280 = true := counterClause955 (baseVal q)

theorem counterClause956 (q : Nat → Bool) : valuationOf q 143 = false ∨ valuationOf q 281 = true := by
  have hs : count281 q = (countLit q [142]) + (countLit q [143]) := List.countP_append (p := literal q) (l₁ := [142]) (l₂ := [143])
  have hm := merge_right (literal (valuationOf q) (143)) (literal (valuationOf q) (281)) (countLit q [142]) (countLit q [143]) (count281 q) 1 (meaning143 q) (meaning281 q) hs
  change valuationOf q 143 = false ∨ valuationOf q 281 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause956 (q : Snake 81) (h : Conditions q) : valuation q 143 = false ∨ valuation q 281 = true := counterClause956 (baseVal q)

theorem counterClause957 (q : Nat → Bool) : valuationOf q 144 = false ∨ valuationOf q 283 = true := by
  have hs : count283 q = (countLit q [144]) + (countLit q [145]) := List.countP_append (p := literal q) (l₁ := [144]) (l₂ := [145])
  have hm := merge_left (literal (valuationOf q) (144)) (literal (valuationOf q) (283)) (countLit q [144]) (countLit q [145]) (count283 q) 1 (meaning144 q) (meaning283 q) hs
  change valuationOf q 144 = false ∨ valuationOf q 283 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause957 (q : Snake 81) (h : Conditions q) : valuation q 144 = false ∨ valuation q 283 = true := counterClause957 (baseVal q)

theorem counterClause958 (q : Nat → Bool) : valuationOf q 283 = false ∨ valuationOf q 285 = true := by
  have hs : count285 q = (countLit q [142, 143]) + (countLit q [144, 145]) := List.countP_append (p := literal q) (l₁ := [142, 143]) (l₂ := [144, 145])
  have hm := merge_right (literal (valuationOf q) (283)) (literal (valuationOf q) (285)) (countLit q [142, 143]) (countLit q [144, 145]) (count285 q) 1 (meaning283 q) (meaning285 q) hs
  change valuationOf q 283 = false ∨ valuationOf q 285 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause958 (q : Snake 81) (h : Conditions q) : valuation q 283 = false ∨ valuation q 285 = true := counterClause958 (baseVal q)

theorem counterClause959 (q : Nat → Bool) : valuationOf q 281 = false ∨ valuationOf q 285 = true := by
  have hs : count285 q = (countLit q [142, 143]) + (countLit q [144, 145]) := List.countP_append (p := literal q) (l₁ := [142, 143]) (l₂ := [144, 145])
  have hm := merge_left (literal (valuationOf q) (281)) (literal (valuationOf q) (285)) (countLit q [142, 143]) (countLit q [144, 145]) (count285 q) 1 (meaning281 q) (meaning285 q) hs
  change valuationOf q 281 = false ∨ valuationOf q 285 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause959 (q : Snake 81) (h : Conditions q) : valuation q 281 = false ∨ valuation q 285 = true := counterClause959 (baseVal q)

theorem counterClause960 (q : Nat → Bool) : valuationOf q 281 = false ∨ valuationOf q 283 = false ∨ valuationOf q 286 = true := by
  have hs : count285 q = (countLit q [142, 143]) + (countLit q [144, 145]) := List.countP_append (p := literal q) (l₁ := [142, 143]) (l₂ := [144, 145])
  have hm := merge_two (literal (valuationOf q) (281)) (literal (valuationOf q) (283)) (literal (valuationOf q) (286)) (countLit q [142, 143]) (countLit q [144, 145]) (count285 q) 1 1 (meaning281 q) (meaning283 q) (meaning286 q) hs
  change valuationOf q 281 = false ∨ valuationOf q 283 = false ∨ valuationOf q 286 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause960 (q : Snake 81) (h : Conditions q) : valuation q 281 = false ∨ valuation q 283 = false ∨ valuation q 286 = true := counterClause960 (baseVal q)

theorem block29 (q : Snake 81) (h : Conditions q) : B112E121.Block29 (valuation q) :=
  ⟨clause929 q h, clause930 q h, clause931 q h, clause932 q h, clause933 q h, clause934 q h, clause935 q h, clause936 q h, clause937 q h, clause938 q h, clause939 q h, clause940 q h, clause941 q h, clause942 q h, clause943 q h, clause944 q h, clause945 q h, clause946 q h, clause947 q h, clause948 q h, clause949 q h, clause950 q h, clause951 q h, clause952 q h, clause953 q h, clause954 q h, clause955 q h, clause956 q h, clause957 q h, clause958 q h, clause959 q h, clause960 q h⟩

end
end Snake9.Regrowth.E112121
