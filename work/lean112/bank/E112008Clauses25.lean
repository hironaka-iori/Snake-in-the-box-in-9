import E112008Semantics
import B112E008Inputs
namespace Snake9.Regrowth.E112008
noncomputable section
local instance blockDec25 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause801 (q : Snake 81) (h : Conditions q) : valuation q 237 = false := by
  rw [value237]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (488 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause802 (q : Snake 81) (h : Conditions q) : valuation q 240 = false := by
  rw [value240]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (494 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause803 (q : Snake 81) (h : Conditions q) : valuation q 243 = false := by
  rw [value243]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (501 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause804 (q : Snake 81) (h : Conditions q) : valuation q 245 = false := by
  rw [value245]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (505 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause805 (q : Snake 81) (h : Conditions q) : valuation q 246 = false := by
  rw [value246]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (506 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem counterClause806 (q : Nat → Bool) : valuationOf q 126 = false ∨ valuationOf q 249 = true := by
  have hs : count249 q = (countLit q [126]) + (countLit q [127]) := List.countP_append (p := literal q) (l₁ := [126]) (l₂ := [127])
  have hm := merge_left (literal (valuationOf q) (126)) (literal (valuationOf q) (249)) (countLit q [126]) (countLit q [127]) (count249 q) 1 (meaning126 q) (meaning249 q) hs
  change valuationOf q 126 = false ∨ valuationOf q 249 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause806 (q : Snake 81) (h : Conditions q) : valuation q 126 = false ∨ valuation q 249 = true := counterClause806 (baseVal q)

theorem counterClause807 (q : Nat → Bool) : valuationOf q 249 = false ∨ valuationOf q 251 = true := by
  have hs : count251 q = (countLit q [125]) + (countLit q [126, 127]) := List.countP_append (p := literal q) (l₁ := [125]) (l₂ := [126, 127])
  have hm := merge_right (literal (valuationOf q) (249)) (literal (valuationOf q) (251)) (countLit q [125]) (countLit q [126, 127]) (count251 q) 1 (meaning249 q) (meaning251 q) hs
  change valuationOf q 249 = false ∨ valuationOf q 251 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause807 (q : Snake 81) (h : Conditions q) : valuation q 249 = false ∨ valuation q 251 = true := counterClause807 (baseVal q)

theorem counterClause808 (q : Nat → Bool) : valuationOf q 125 = false ∨ valuationOf q 251 = true := by
  have hs : count251 q = (countLit q [125]) + (countLit q [126, 127]) := List.countP_append (p := literal q) (l₁ := [125]) (l₂ := [126, 127])
  have hm := merge_left (literal (valuationOf q) (125)) (literal (valuationOf q) (251)) (countLit q [125]) (countLit q [126, 127]) (count251 q) 1 (meaning125 q) (meaning251 q) hs
  change valuationOf q 125 = false ∨ valuationOf q 251 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause808 (q : Snake 81) (h : Conditions q) : valuation q 125 = false ∨ valuation q 251 = true := counterClause808 (baseVal q)

theorem counterClause809 (q : Nat → Bool) : valuationOf q 128 = false ∨ valuationOf q 253 = true := by
  have hs : count253 q = (countLit q [128]) + (countLit q [129]) := List.countP_append (p := literal q) (l₁ := [128]) (l₂ := [129])
  have hm := merge_left (literal (valuationOf q) (128)) (literal (valuationOf q) (253)) (countLit q [128]) (countLit q [129]) (count253 q) 1 (meaning128 q) (meaning253 q) hs
  change valuationOf q 128 = false ∨ valuationOf q 253 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause809 (q : Snake 81) (h : Conditions q) : valuation q 128 = false ∨ valuation q 253 = true := counterClause809 (baseVal q)

theorem counterClause810 (q : Nat → Bool) : valuationOf q 131 = false ∨ valuationOf q 255 = true := by
  have hs : count255 q = (countLit q [130]) + (countLit q [131]) := List.countP_append (p := literal q) (l₁ := [130]) (l₂ := [131])
  have hm := merge_right (literal (valuationOf q) (131)) (literal (valuationOf q) (255)) (countLit q [130]) (countLit q [131]) (count255 q) 1 (meaning131 q) (meaning255 q) hs
  change valuationOf q 131 = false ∨ valuationOf q 255 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause810 (q : Snake 81) (h : Conditions q) : valuation q 131 = false ∨ valuation q 255 = true := counterClause810 (baseVal q)

theorem counterClause811 (q : Nat → Bool) : valuationOf q 255 = false ∨ valuationOf q 257 = true := by
  have hs : count257 q = (countLit q [128, 129]) + (countLit q [130, 131]) := List.countP_append (p := literal q) (l₁ := [128, 129]) (l₂ := [130, 131])
  have hm := merge_right (literal (valuationOf q) (255)) (literal (valuationOf q) (257)) (countLit q [128, 129]) (countLit q [130, 131]) (count257 q) 1 (meaning255 q) (meaning257 q) hs
  change valuationOf q 255 = false ∨ valuationOf q 257 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause811 (q : Snake 81) (h : Conditions q) : valuation q 255 = false ∨ valuation q 257 = true := counterClause811 (baseVal q)

theorem counterClause812 (q : Nat → Bool) : valuationOf q 253 = false ∨ valuationOf q 255 = false ∨ valuationOf q 258 = true := by
  have hs : count257 q = (countLit q [128, 129]) + (countLit q [130, 131]) := List.countP_append (p := literal q) (l₁ := [128, 129]) (l₂ := [130, 131])
  have hm := merge_two (literal (valuationOf q) (253)) (literal (valuationOf q) (255)) (literal (valuationOf q) (258)) (countLit q [128, 129]) (countLit q [130, 131]) (count257 q) 1 1 (meaning253 q) (meaning255 q) (meaning258 q) hs
  change valuationOf q 253 = false ∨ valuationOf q 255 = false ∨ valuationOf q 258 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause812 (q : Snake 81) (h : Conditions q) : valuation q 253 = false ∨ valuation q 255 = false ∨ valuation q 258 = true := counterClause812 (baseVal q)

theorem counterClause813 (q : Nat → Bool) : valuationOf q 257 = false ∨ valuationOf q 259 = true := by
  have hs : count259 q = (countLit q [125, 126, 127]) + (countLit q [128, 129, 130, 131]) := List.countP_append (p := literal q) (l₁ := [125, 126, 127]) (l₂ := [128, 129, 130, 131])
  have hm := merge_right (literal (valuationOf q) (257)) (literal (valuationOf q) (259)) (countLit q [125, 126, 127]) (countLit q [128, 129, 130, 131]) (count259 q) 1 (meaning257 q) (meaning259 q) hs
  change valuationOf q 257 = false ∨ valuationOf q 259 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause813 (q : Snake 81) (h : Conditions q) : valuation q 257 = false ∨ valuation q 259 = true := counterClause813 (baseVal q)

theorem counterClause814 (q : Nat → Bool) : valuationOf q 258 = false ∨ valuationOf q 260 = true := by
  have hs : count259 q = (countLit q [125, 126, 127]) + (countLit q [128, 129, 130, 131]) := List.countP_append (p := literal q) (l₁ := [125, 126, 127]) (l₂ := [128, 129, 130, 131])
  have hm := merge_right (literal (valuationOf q) (258)) (literal (valuationOf q) (260)) (countLit q [125, 126, 127]) (countLit q [128, 129, 130, 131]) (count259 q) 2 (meaning258 q) (meaning260 q) hs
  change valuationOf q 258 = false ∨ valuationOf q 260 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause814 (q : Snake 81) (h : Conditions q) : valuation q 258 = false ∨ valuation q 260 = true := counterClause814 (baseVal q)

theorem counterClause815 (q : Nat → Bool) : valuationOf q 251 = false ∨ valuationOf q 259 = true := by
  have hs : count259 q = (countLit q [125, 126, 127]) + (countLit q [128, 129, 130, 131]) := List.countP_append (p := literal q) (l₁ := [125, 126, 127]) (l₂ := [128, 129, 130, 131])
  have hm := merge_left (literal (valuationOf q) (251)) (literal (valuationOf q) (259)) (countLit q [125, 126, 127]) (countLit q [128, 129, 130, 131]) (count259 q) 1 (meaning251 q) (meaning259 q) hs
  change valuationOf q 251 = false ∨ valuationOf q 259 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause815 (q : Snake 81) (h : Conditions q) : valuation q 251 = false ∨ valuation q 259 = true := counterClause815 (baseVal q)

theorem counterClause816 (q : Nat → Bool) : valuationOf q 251 = false ∨ valuationOf q 257 = false ∨ valuationOf q 260 = true := by
  have hs : count259 q = (countLit q [125, 126, 127]) + (countLit q [128, 129, 130, 131]) := List.countP_append (p := literal q) (l₁ := [125, 126, 127]) (l₂ := [128, 129, 130, 131])
  have hm := merge_two (literal (valuationOf q) (251)) (literal (valuationOf q) (257)) (literal (valuationOf q) (260)) (countLit q [125, 126, 127]) (countLit q [128, 129, 130, 131]) (count259 q) 1 1 (meaning251 q) (meaning257 q) (meaning260 q) hs
  change valuationOf q 251 = false ∨ valuationOf q 257 = false ∨ valuationOf q 260 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause816 (q : Snake 81) (h : Conditions q) : valuation q 251 = false ∨ valuation q 257 = false ∨ valuation q 260 = true := counterClause816 (baseVal q)

theorem counterClause817 (q : Nat → Bool) : valuationOf q 133 = false ∨ valuationOf q 261 = true := by
  have hs : count261 q = (countLit q [132]) + (countLit q [133]) := List.countP_append (p := literal q) (l₁ := [132]) (l₂ := [133])
  have hm := merge_right (literal (valuationOf q) (133)) (literal (valuationOf q) (261)) (countLit q [132]) (countLit q [133]) (count261 q) 1 (meaning133 q) (meaning261 q) hs
  change valuationOf q 133 = false ∨ valuationOf q 261 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause817 (q : Snake 81) (h : Conditions q) : valuation q 133 = false ∨ valuation q 261 = true := counterClause817 (baseVal q)

theorem counterClause818 (q : Nat → Bool) : valuationOf q 135 = false ∨ valuationOf q 263 = true := by
  have hs : count263 q = (countLit q [134]) + (countLit q [135]) := List.countP_append (p := literal q) (l₁ := [134]) (l₂ := [135])
  have hm := merge_right (literal (valuationOf q) (135)) (literal (valuationOf q) (263)) (countLit q [134]) (countLit q [135]) (count263 q) 1 (meaning135 q) (meaning263 q) hs
  change valuationOf q 135 = false ∨ valuationOf q 263 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause818 (q : Snake 81) (h : Conditions q) : valuation q 135 = false ∨ valuation q 263 = true := counterClause818 (baseVal q)

theorem counterClause819 (q : Nat → Bool) : valuationOf q 263 = false ∨ valuationOf q 265 = true := by
  have hs : count265 q = (countLit q [132, 133]) + (countLit q [134, 135]) := List.countP_append (p := literal q) (l₁ := [132, 133]) (l₂ := [134, 135])
  have hm := merge_right (literal (valuationOf q) (263)) (literal (valuationOf q) (265)) (countLit q [132, 133]) (countLit q [134, 135]) (count265 q) 1 (meaning263 q) (meaning265 q) hs
  change valuationOf q 263 = false ∨ valuationOf q 265 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause819 (q : Snake 81) (h : Conditions q) : valuation q 263 = false ∨ valuation q 265 = true := counterClause819 (baseVal q)

theorem counterClause820 (q : Nat → Bool) : valuationOf q 261 = false ∨ valuationOf q 265 = true := by
  have hs : count265 q = (countLit q [132, 133]) + (countLit q [134, 135]) := List.countP_append (p := literal q) (l₁ := [132, 133]) (l₂ := [134, 135])
  have hm := merge_left (literal (valuationOf q) (261)) (literal (valuationOf q) (265)) (countLit q [132, 133]) (countLit q [134, 135]) (count265 q) 1 (meaning261 q) (meaning265 q) hs
  change valuationOf q 261 = false ∨ valuationOf q 265 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause820 (q : Snake 81) (h : Conditions q) : valuation q 261 = false ∨ valuation q 265 = true := counterClause820 (baseVal q)

theorem counterClause821 (q : Nat → Bool) : valuationOf q 265 = false ∨ valuationOf q 273 = true := by
  have hs : count273 q = (countLit q [132, 133, 134, 135]) + (countLit q [136, 137, 138, 139]) := List.countP_append (p := literal q) (l₁ := [132, 133, 134, 135]) (l₂ := [136, 137, 138, 139])
  have hm := merge_left (literal (valuationOf q) (265)) (literal (valuationOf q) (273)) (countLit q [132, 133, 134, 135]) (countLit q [136, 137, 138, 139]) (count273 q) 1 (meaning265 q) (meaning273 q) hs
  change valuationOf q 265 = false ∨ valuationOf q 273 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause821 (q : Snake 81) (h : Conditions q) : valuation q 265 = false ∨ valuation q 273 = true := counterClause821 (baseVal q)

theorem counterClause822 (q : Nat → Bool) : valuationOf q 273 = false ∨ valuationOf q 275 = true := by
  have hs : count275 q = (countLit q [125, 126, 127, 128, 129, 130, 131]) + (countLit q [132, 133, 134, 135, 136, 137, 138, 139]) := List.countP_append (p := literal q) (l₁ := [125, 126, 127, 128, 129, 130, 131]) (l₂ := [132, 133, 134, 135, 136, 137, 138, 139])
  have hm := merge_right (literal (valuationOf q) (273)) (literal (valuationOf q) (275)) (countLit q [125, 126, 127, 128, 129, 130, 131]) (countLit q [132, 133, 134, 135, 136, 137, 138, 139]) (count275 q) 1 (meaning273 q) (meaning275 q) hs
  change valuationOf q 273 = false ∨ valuationOf q 275 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause822 (q : Snake 81) (h : Conditions q) : valuation q 273 = false ∨ valuation q 275 = true := counterClause822 (baseVal q)

theorem counterClause823 (q : Nat → Bool) : valuationOf q 259 = false ∨ valuationOf q 275 = true := by
  have hs : count275 q = (countLit q [125, 126, 127, 128, 129, 130, 131]) + (countLit q [132, 133, 134, 135, 136, 137, 138, 139]) := List.countP_append (p := literal q) (l₁ := [125, 126, 127, 128, 129, 130, 131]) (l₂ := [132, 133, 134, 135, 136, 137, 138, 139])
  have hm := merge_left (literal (valuationOf q) (259)) (literal (valuationOf q) (275)) (countLit q [125, 126, 127, 128, 129, 130, 131]) (countLit q [132, 133, 134, 135, 136, 137, 138, 139]) (count275 q) 1 (meaning259 q) (meaning275 q) hs
  change valuationOf q 259 = false ∨ valuationOf q 275 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause823 (q : Snake 81) (h : Conditions q) : valuation q 259 = false ∨ valuation q 275 = true := counterClause823 (baseVal q)

theorem counterClause824 (q : Nat → Bool) : valuationOf q 259 = false ∨ valuationOf q 273 = false ∨ valuationOf q 276 = true := by
  have hs : count275 q = (countLit q [125, 126, 127, 128, 129, 130, 131]) + (countLit q [132, 133, 134, 135, 136, 137, 138, 139]) := List.countP_append (p := literal q) (l₁ := [125, 126, 127, 128, 129, 130, 131]) (l₂ := [132, 133, 134, 135, 136, 137, 138, 139])
  have hm := merge_two (literal (valuationOf q) (259)) (literal (valuationOf q) (273)) (literal (valuationOf q) (276)) (countLit q [125, 126, 127, 128, 129, 130, 131]) (countLit q [132, 133, 134, 135, 136, 137, 138, 139]) (count275 q) 1 1 (meaning259 q) (meaning273 q) (meaning276 q) hs
  change valuationOf q 259 = false ∨ valuationOf q 273 = false ∨ valuationOf q 276 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause824 (q : Snake 81) (h : Conditions q) : valuation q 259 = false ∨ valuation q 273 = false ∨ valuation q 276 = true := counterClause824 (baseVal q)

theorem counterClause825 (q : Nat → Bool) : valuationOf q 260 = false ∨ valuationOf q 276 = true := by
  have hs : count275 q = (countLit q [125, 126, 127, 128, 129, 130, 131]) + (countLit q [132, 133, 134, 135, 136, 137, 138, 139]) := List.countP_append (p := literal q) (l₁ := [125, 126, 127, 128, 129, 130, 131]) (l₂ := [132, 133, 134, 135, 136, 137, 138, 139])
  have hm := merge_left (literal (valuationOf q) (260)) (literal (valuationOf q) (276)) (countLit q [125, 126, 127, 128, 129, 130, 131]) (countLit q [132, 133, 134, 135, 136, 137, 138, 139]) (count275 q) 2 (meaning260 q) (meaning276 q) hs
  change valuationOf q 260 = false ∨ valuationOf q 276 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause825 (q : Snake 81) (h : Conditions q) : valuation q 260 = false ∨ valuation q 276 = true := counterClause825 (baseVal q)

theorem counterClause826 (q : Nat → Bool) : valuationOf q 142 = false ∨ valuationOf q 277 = true := by
  have hs : count277 q = (countLit q [141]) + (countLit q [142]) := List.countP_append (p := literal q) (l₁ := [141]) (l₂ := [142])
  have hm := merge_right (literal (valuationOf q) (142)) (literal (valuationOf q) (277)) (countLit q [141]) (countLit q [142]) (count277 q) 1 (meaning142 q) (meaning277 q) hs
  change valuationOf q 142 = false ∨ valuationOf q 277 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause826 (q : Snake 81) (h : Conditions q) : valuation q 142 = false ∨ valuation q 277 = true := counterClause826 (baseVal q)

theorem counterClause827 (q : Nat → Bool) : valuationOf q 277 = false ∨ valuationOf q 279 = true := by
  have hs : count279 q = (countLit q [140]) + (countLit q [141, 142]) := List.countP_append (p := literal q) (l₁ := [140]) (l₂ := [141, 142])
  have hm := merge_right (literal (valuationOf q) (277)) (literal (valuationOf q) (279)) (countLit q [140]) (countLit q [141, 142]) (count279 q) 1 (meaning277 q) (meaning279 q) hs
  change valuationOf q 277 = false ∨ valuationOf q 279 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause827 (q : Snake 81) (h : Conditions q) : valuation q 277 = false ∨ valuation q 279 = true := counterClause827 (baseVal q)

theorem counterClause828 (q : Nat → Bool) : valuationOf q 140 = false ∨ valuationOf q 279 = true := by
  have hs : count279 q = (countLit q [140]) + (countLit q [141, 142]) := List.countP_append (p := literal q) (l₁ := [140]) (l₂ := [141, 142])
  have hm := merge_left (literal (valuationOf q) (140)) (literal (valuationOf q) (279)) (countLit q [140]) (countLit q [141, 142]) (count279 q) 1 (meaning140 q) (meaning279 q) hs
  change valuationOf q 140 = false ∨ valuationOf q 279 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause828 (q : Snake 81) (h : Conditions q) : valuation q 140 = false ∨ valuation q 279 = true := counterClause828 (baseVal q)

theorem counterClause829 (q : Nat → Bool) : valuationOf q 140 = false ∨ valuationOf q 277 = false ∨ valuationOf q 280 = true := by
  have hs : count279 q = (countLit q [140]) + (countLit q [141, 142]) := List.countP_append (p := literal q) (l₁ := [140]) (l₂ := [141, 142])
  have hm := merge_two (literal (valuationOf q) (140)) (literal (valuationOf q) (277)) (literal (valuationOf q) (280)) (countLit q [140]) (countLit q [141, 142]) (count279 q) 1 1 (meaning140 q) (meaning277 q) (meaning280 q) hs
  change valuationOf q 140 = false ∨ valuationOf q 277 = false ∨ valuationOf q 280 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause829 (q : Snake 81) (h : Conditions q) : valuation q 140 = false ∨ valuation q 277 = false ∨ valuation q 280 = true := counterClause829 (baseVal q)

theorem counterClause830 (q : Nat → Bool) : valuationOf q 146 = false ∨ valuationOf q 283 = true := by
  have hs : count283 q = (countLit q [145]) + (countLit q [146]) := List.countP_append (p := literal q) (l₁ := [145]) (l₂ := [146])
  have hm := merge_right (literal (valuationOf q) (146)) (literal (valuationOf q) (283)) (countLit q [145]) (countLit q [146]) (count283 q) 1 (meaning146 q) (meaning283 q) hs
  change valuationOf q 146 = false ∨ valuationOf q 283 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause830 (q : Snake 81) (h : Conditions q) : valuation q 146 = false ∨ valuation q 283 = true := counterClause830 (baseVal q)

theorem counterClause831 (q : Nat → Bool) : valuationOf q 283 = false ∨ valuationOf q 285 = true := by
  have hs : count285 q = (countLit q [143, 144]) + (countLit q [145, 146]) := List.countP_append (p := literal q) (l₁ := [143, 144]) (l₂ := [145, 146])
  have hm := merge_right (literal (valuationOf q) (283)) (literal (valuationOf q) (285)) (countLit q [143, 144]) (countLit q [145, 146]) (count285 q) 1 (meaning283 q) (meaning285 q) hs
  change valuationOf q 283 = false ∨ valuationOf q 285 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause831 (q : Snake 81) (h : Conditions q) : valuation q 283 = false ∨ valuation q 285 = true := counterClause831 (baseVal q)

theorem counterClause832 (q : Nat → Bool) : valuationOf q 285 = false ∨ valuationOf q 287 = true := by
  have hs : count287 q = (countLit q [140, 141, 142]) + (countLit q [143, 144, 145, 146]) := List.countP_append (p := literal q) (l₁ := [140, 141, 142]) (l₂ := [143, 144, 145, 146])
  have hm := merge_right (literal (valuationOf q) (285)) (literal (valuationOf q) (287)) (countLit q [140, 141, 142]) (countLit q [143, 144, 145, 146]) (count287 q) 1 (meaning285 q) (meaning287 q) hs
  change valuationOf q 285 = false ∨ valuationOf q 287 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause832 (q : Snake 81) (h : Conditions q) : valuation q 285 = false ∨ valuation q 287 = true := counterClause832 (baseVal q)

theorem block25 (q : Snake 81) (h : Conditions q) : B112E008.Block25 (valuation q) :=
  ⟨clause801 q h, clause802 q h, clause803 q h, clause804 q h, clause805 q h, clause806 q h, clause807 q h, clause808 q h, clause809 q h, clause810 q h, clause811 q h, clause812 q h, clause813 q h, clause814 q h, clause815 q h, clause816 q h, clause817 q h, clause818 q h, clause819 q h, clause820 q h, clause821 q h, clause822 q h, clause823 q h, clause824 q h, clause825 q h, clause826 q h, clause827 q h, clause828 q h, clause829 q h, clause830 q h, clause831 q h, clause832 q h⟩

end
end Snake9.Regrowth.E112008
