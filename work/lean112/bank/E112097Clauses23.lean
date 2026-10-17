import E112097Semantics
import B112E097Inputs
namespace Snake9.Regrowth.E112097
noncomputable section
local instance blockDec23 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause737 (q : Snake 81) (h : Conditions q) : valuation q 236 = false := by
  rw [value236]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (495 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause738 (q : Snake 81) (h : Conditions q) : valuation q 237 = false := by
  rw [value237]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (497 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause739 (q : Snake 81) (h : Conditions q) : valuation q 238 = false := by
  rw [value238]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (500 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause740 (q : Snake 81) (h : Conditions q) : valuation q 241 = false := by
  rw [value241]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (503 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause741 (q : Snake 81) (h : Conditions q) : valuation q 244 = false := by
  rw [value244]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (507 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem counterClause742 (q : Nat → Bool) : valuationOf q 125 = false ∨ valuationOf q 247 = true := by
  have hs : count247 q = (countLit q [125]) + (countLit q [126]) := List.countP_append (p := literal q) (l₁ := [125]) (l₂ := [126])
  have hm := merge_left (literal (valuationOf q) (125)) (literal (valuationOf q) (247)) (countLit q [125]) (countLit q [126]) (count247 q) 1 (meaning125 q) (meaning247 q) hs
  change valuationOf q 125 = false ∨ valuationOf q 247 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause742 (q : Snake 81) (h : Conditions q) : valuation q 125 = false ∨ valuation q 247 = true := counterClause742 (baseVal q)

theorem counterClause743 (q : Nat → Bool) : valuationOf q 247 = false ∨ valuationOf q 249 = true := by
  have hs : count249 q = (countLit q [124]) + (countLit q [125, 126]) := List.countP_append (p := literal q) (l₁ := [124]) (l₂ := [125, 126])
  have hm := merge_right (literal (valuationOf q) (247)) (literal (valuationOf q) (249)) (countLit q [124]) (countLit q [125, 126]) (count249 q) 1 (meaning247 q) (meaning249 q) hs
  change valuationOf q 247 = false ∨ valuationOf q 249 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause743 (q : Snake 81) (h : Conditions q) : valuation q 247 = false ∨ valuation q 249 = true := counterClause743 (baseVal q)

theorem counterClause744 (q : Nat → Bool) : valuationOf q 128 = false ∨ valuationOf q 251 = true := by
  have hs : count251 q = (countLit q [127]) + (countLit q [128]) := List.countP_append (p := literal q) (l₁ := [127]) (l₂ := [128])
  have hm := merge_right (literal (valuationOf q) (128)) (literal (valuationOf q) (251)) (countLit q [127]) (countLit q [128]) (count251 q) 1 (meaning128 q) (meaning251 q) hs
  change valuationOf q 128 = false ∨ valuationOf q 251 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause744 (q : Snake 81) (h : Conditions q) : valuation q 128 = false ∨ valuation q 251 = true := counterClause744 (baseVal q)

theorem counterClause745 (q : Nat → Bool) : valuationOf q 251 = false ∨ valuationOf q 255 = true := by
  have hs : count255 q = (countLit q [127, 128]) + (countLit q [129, 130]) := List.countP_append (p := literal q) (l₁ := [127, 128]) (l₂ := [129, 130])
  have hm := merge_left (literal (valuationOf q) (251)) (literal (valuationOf q) (255)) (countLit q [127, 128]) (countLit q [129, 130]) (count255 q) 1 (meaning251 q) (meaning255 q) hs
  change valuationOf q 251 = false ∨ valuationOf q 255 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause745 (q : Snake 81) (h : Conditions q) : valuation q 251 = false ∨ valuation q 255 = true := counterClause745 (baseVal q)

theorem counterClause746 (q : Nat → Bool) : valuationOf q 255 = false ∨ valuationOf q 257 = true := by
  have hs : count257 q = (countLit q [124, 125, 126]) + (countLit q [127, 128, 129, 130]) := List.countP_append (p := literal q) (l₁ := [124, 125, 126]) (l₂ := [127, 128, 129, 130])
  have hm := merge_right (literal (valuationOf q) (255)) (literal (valuationOf q) (257)) (countLit q [124, 125, 126]) (countLit q [127, 128, 129, 130]) (count257 q) 1 (meaning255 q) (meaning257 q) hs
  change valuationOf q 255 = false ∨ valuationOf q 257 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause746 (q : Snake 81) (h : Conditions q) : valuation q 255 = false ∨ valuation q 257 = true := counterClause746 (baseVal q)

theorem counterClause747 (q : Nat → Bool) : valuationOf q 249 = false ∨ valuationOf q 257 = true := by
  have hs : count257 q = (countLit q [124, 125, 126]) + (countLit q [127, 128, 129, 130]) := List.countP_append (p := literal q) (l₁ := [124, 125, 126]) (l₂ := [127, 128, 129, 130])
  have hm := merge_left (literal (valuationOf q) (249)) (literal (valuationOf q) (257)) (countLit q [124, 125, 126]) (countLit q [127, 128, 129, 130]) (count257 q) 1 (meaning249 q) (meaning257 q) hs
  change valuationOf q 249 = false ∨ valuationOf q 257 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause747 (q : Snake 81) (h : Conditions q) : valuation q 249 = false ∨ valuation q 257 = true := counterClause747 (baseVal q)

theorem counterClause748 (q : Nat → Bool) : valuationOf q 249 = false ∨ valuationOf q 255 = false ∨ valuationOf q 258 = true := by
  have hs : count257 q = (countLit q [124, 125, 126]) + (countLit q [127, 128, 129, 130]) := List.countP_append (p := literal q) (l₁ := [124, 125, 126]) (l₂ := [127, 128, 129, 130])
  have hm := merge_two (literal (valuationOf q) (249)) (literal (valuationOf q) (255)) (literal (valuationOf q) (258)) (countLit q [124, 125, 126]) (countLit q [127, 128, 129, 130]) (count257 q) 1 1 (meaning249 q) (meaning255 q) (meaning258 q) hs
  change valuationOf q 249 = false ∨ valuationOf q 255 = false ∨ valuationOf q 258 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause748 (q : Snake 81) (h : Conditions q) : valuation q 249 = false ∨ valuation q 255 = false ∨ valuation q 258 = true := counterClause748 (baseVal q)

theorem counterClause749 (q : Nat → Bool) : valuationOf q 132 = false ∨ valuationOf q 259 = true := by
  have hs : count259 q = (countLit q [131]) + (countLit q [132]) := List.countP_append (p := literal q) (l₁ := [131]) (l₂ := [132])
  have hm := merge_right (literal (valuationOf q) (132)) (literal (valuationOf q) (259)) (countLit q [131]) (countLit q [132]) (count259 q) 1 (meaning132 q) (meaning259 q) hs
  change valuationOf q 132 = false ∨ valuationOf q 259 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause749 (q : Snake 81) (h : Conditions q) : valuation q 132 = false ∨ valuation q 259 = true := counterClause749 (baseVal q)

theorem counterClause750 (q : Nat → Bool) : valuationOf q 134 = false ∨ valuationOf q 261 = true := by
  have hs : count261 q = (countLit q [133]) + (countLit q [134]) := List.countP_append (p := literal q) (l₁ := [133]) (l₂ := [134])
  have hm := merge_right (literal (valuationOf q) (134)) (literal (valuationOf q) (261)) (countLit q [133]) (countLit q [134]) (count261 q) 1 (meaning134 q) (meaning261 q) hs
  change valuationOf q 134 = false ∨ valuationOf q 261 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause750 (q : Snake 81) (h : Conditions q) : valuation q 134 = false ∨ valuation q 261 = true := counterClause750 (baseVal q)

theorem counterClause751 (q : Nat → Bool) : valuationOf q 261 = false ∨ valuationOf q 263 = true := by
  have hs : count263 q = (countLit q [131, 132]) + (countLit q [133, 134]) := List.countP_append (p := literal q) (l₁ := [131, 132]) (l₂ := [133, 134])
  have hm := merge_right (literal (valuationOf q) (261)) (literal (valuationOf q) (263)) (countLit q [131, 132]) (countLit q [133, 134]) (count263 q) 1 (meaning261 q) (meaning263 q) hs
  change valuationOf q 261 = false ∨ valuationOf q 263 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause751 (q : Snake 81) (h : Conditions q) : valuation q 261 = false ∨ valuation q 263 = true := counterClause751 (baseVal q)

theorem counterClause752 (q : Nat → Bool) : valuationOf q 259 = false ∨ valuationOf q 263 = true := by
  have hs : count263 q = (countLit q [131, 132]) + (countLit q [133, 134]) := List.countP_append (p := literal q) (l₁ := [131, 132]) (l₂ := [133, 134])
  have hm := merge_left (literal (valuationOf q) (259)) (literal (valuationOf q) (263)) (countLit q [131, 132]) (countLit q [133, 134]) (count263 q) 1 (meaning259 q) (meaning263 q) hs
  change valuationOf q 259 = false ∨ valuationOf q 263 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause752 (q : Snake 81) (h : Conditions q) : valuation q 259 = false ∨ valuation q 263 = true := counterClause752 (baseVal q)

theorem counterClause753 (q : Nat → Bool) : valuationOf q 135 = false ∨ valuationOf q 265 = true := by
  have hs : count265 q = (countLit q [135]) + (countLit q [136]) := List.countP_append (p := literal q) (l₁ := [135]) (l₂ := [136])
  have hm := merge_left (literal (valuationOf q) (135)) (literal (valuationOf q) (265)) (countLit q [135]) (countLit q [136]) (count265 q) 1 (meaning135 q) (meaning265 q) hs
  change valuationOf q 135 = false ∨ valuationOf q 265 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause753 (q : Snake 81) (h : Conditions q) : valuation q 135 = false ∨ valuation q 265 = true := counterClause753 (baseVal q)

theorem counterClause754 (q : Nat → Bool) : valuationOf q 138 = false ∨ valuationOf q 267 = true := by
  have hs : count267 q = (countLit q [137]) + (countLit q [138]) := List.countP_append (p := literal q) (l₁ := [137]) (l₂ := [138])
  have hm := merge_right (literal (valuationOf q) (138)) (literal (valuationOf q) (267)) (countLit q [137]) (countLit q [138]) (count267 q) 1 (meaning138 q) (meaning267 q) hs
  change valuationOf q 138 = false ∨ valuationOf q 267 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause754 (q : Snake 81) (h : Conditions q) : valuation q 138 = false ∨ valuation q 267 = true := counterClause754 (baseVal q)

theorem counterClause755 (q : Nat → Bool) : valuationOf q 137 = false ∨ valuationOf q 267 = true := by
  have hs : count267 q = (countLit q [137]) + (countLit q [138]) := List.countP_append (p := literal q) (l₁ := [137]) (l₂ := [138])
  have hm := merge_left (literal (valuationOf q) (137)) (literal (valuationOf q) (267)) (countLit q [137]) (countLit q [138]) (count267 q) 1 (meaning137 q) (meaning267 q) hs
  change valuationOf q 137 = false ∨ valuationOf q 267 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause755 (q : Snake 81) (h : Conditions q) : valuation q 137 = false ∨ valuation q 267 = true := counterClause755 (baseVal q)

theorem counterClause756 (q : Nat → Bool) : valuationOf q 267 = false ∨ valuationOf q 269 = true := by
  have hs : count269 q = (countLit q [135, 136]) + (countLit q [137, 138]) := List.countP_append (p := literal q) (l₁ := [135, 136]) (l₂ := [137, 138])
  have hm := merge_right (literal (valuationOf q) (267)) (literal (valuationOf q) (269)) (countLit q [135, 136]) (countLit q [137, 138]) (count269 q) 1 (meaning267 q) (meaning269 q) hs
  change valuationOf q 267 = false ∨ valuationOf q 269 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause756 (q : Snake 81) (h : Conditions q) : valuation q 267 = false ∨ valuation q 269 = true := counterClause756 (baseVal q)

theorem counterClause757 (q : Nat → Bool) : valuationOf q 265 = false ∨ valuationOf q 269 = true := by
  have hs : count269 q = (countLit q [135, 136]) + (countLit q [137, 138]) := List.countP_append (p := literal q) (l₁ := [135, 136]) (l₂ := [137, 138])
  have hm := merge_left (literal (valuationOf q) (265)) (literal (valuationOf q) (269)) (countLit q [135, 136]) (countLit q [137, 138]) (count269 q) 1 (meaning265 q) (meaning269 q) hs
  change valuationOf q 265 = false ∨ valuationOf q 269 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause757 (q : Snake 81) (h : Conditions q) : valuation q 265 = false ∨ valuation q 269 = true := counterClause757 (baseVal q)

theorem counterClause758 (q : Nat → Bool) : valuationOf q 265 = false ∨ valuationOf q 267 = false ∨ valuationOf q 270 = true := by
  have hs : count269 q = (countLit q [135, 136]) + (countLit q [137, 138]) := List.countP_append (p := literal q) (l₁ := [135, 136]) (l₂ := [137, 138])
  have hm := merge_two (literal (valuationOf q) (265)) (literal (valuationOf q) (267)) (literal (valuationOf q) (270)) (countLit q [135, 136]) (countLit q [137, 138]) (count269 q) 1 1 (meaning265 q) (meaning267 q) (meaning270 q) hs
  change valuationOf q 265 = false ∨ valuationOf q 267 = false ∨ valuationOf q 270 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause758 (q : Snake 81) (h : Conditions q) : valuation q 265 = false ∨ valuation q 267 = false ∨ valuation q 270 = true := counterClause758 (baseVal q)

theorem counterClause759 (q : Nat → Bool) : valuationOf q 269 = false ∨ valuationOf q 271 = true := by
  have hs : count271 q = (countLit q [131, 132, 133, 134]) + (countLit q [135, 136, 137, 138]) := List.countP_append (p := literal q) (l₁ := [131, 132, 133, 134]) (l₂ := [135, 136, 137, 138])
  have hm := merge_right (literal (valuationOf q) (269)) (literal (valuationOf q) (271)) (countLit q [131, 132, 133, 134]) (countLit q [135, 136, 137, 138]) (count271 q) 1 (meaning269 q) (meaning271 q) hs
  change valuationOf q 269 = false ∨ valuationOf q 271 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause759 (q : Snake 81) (h : Conditions q) : valuation q 269 = false ∨ valuation q 271 = true := counterClause759 (baseVal q)

theorem counterClause760 (q : Nat → Bool) : valuationOf q 270 = false ∨ valuationOf q 272 = true := by
  have hs : count271 q = (countLit q [131, 132, 133, 134]) + (countLit q [135, 136, 137, 138]) := List.countP_append (p := literal q) (l₁ := [131, 132, 133, 134]) (l₂ := [135, 136, 137, 138])
  have hm := merge_right (literal (valuationOf q) (270)) (literal (valuationOf q) (272)) (countLit q [131, 132, 133, 134]) (countLit q [135, 136, 137, 138]) (count271 q) 2 (meaning270 q) (meaning272 q) hs
  change valuationOf q 270 = false ∨ valuationOf q 272 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause760 (q : Snake 81) (h : Conditions q) : valuation q 270 = false ∨ valuation q 272 = true := counterClause760 (baseVal q)

theorem counterClause761 (q : Nat → Bool) : valuationOf q 263 = false ∨ valuationOf q 271 = true := by
  have hs : count271 q = (countLit q [131, 132, 133, 134]) + (countLit q [135, 136, 137, 138]) := List.countP_append (p := literal q) (l₁ := [131, 132, 133, 134]) (l₂ := [135, 136, 137, 138])
  have hm := merge_left (literal (valuationOf q) (263)) (literal (valuationOf q) (271)) (countLit q [131, 132, 133, 134]) (countLit q [135, 136, 137, 138]) (count271 q) 1 (meaning263 q) (meaning271 q) hs
  change valuationOf q 263 = false ∨ valuationOf q 271 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause761 (q : Snake 81) (h : Conditions q) : valuation q 263 = false ∨ valuation q 271 = true := counterClause761 (baseVal q)

theorem counterClause762 (q : Nat → Bool) : valuationOf q 271 = false ∨ valuationOf q 273 = true := by
  have hs : count273 q = (countLit q [124, 125, 126, 127, 128, 129, 130]) + (countLit q [131, 132, 133, 134, 135, 136, 137, 138]) := List.countP_append (p := literal q) (l₁ := [124, 125, 126, 127, 128, 129, 130]) (l₂ := [131, 132, 133, 134, 135, 136, 137, 138])
  have hm := merge_right (literal (valuationOf q) (271)) (literal (valuationOf q) (273)) (countLit q [124, 125, 126, 127, 128, 129, 130]) (countLit q [131, 132, 133, 134, 135, 136, 137, 138]) (count273 q) 1 (meaning271 q) (meaning273 q) hs
  change valuationOf q 271 = false ∨ valuationOf q 273 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause762 (q : Snake 81) (h : Conditions q) : valuation q 271 = false ∨ valuation q 273 = true := counterClause762 (baseVal q)

theorem counterClause763 (q : Nat → Bool) : valuationOf q 272 = false ∨ valuationOf q 274 = true := by
  have hs : count273 q = (countLit q [124, 125, 126, 127, 128, 129, 130]) + (countLit q [131, 132, 133, 134, 135, 136, 137, 138]) := List.countP_append (p := literal q) (l₁ := [124, 125, 126, 127, 128, 129, 130]) (l₂ := [131, 132, 133, 134, 135, 136, 137, 138])
  have hm := merge_right (literal (valuationOf q) (272)) (literal (valuationOf q) (274)) (countLit q [124, 125, 126, 127, 128, 129, 130]) (countLit q [131, 132, 133, 134, 135, 136, 137, 138]) (count273 q) 2 (meaning272 q) (meaning274 q) hs
  change valuationOf q 272 = false ∨ valuationOf q 274 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause763 (q : Snake 81) (h : Conditions q) : valuation q 272 = false ∨ valuation q 274 = true := counterClause763 (baseVal q)

theorem counterClause764 (q : Nat → Bool) : valuationOf q 257 = false ∨ valuationOf q 273 = true := by
  have hs : count273 q = (countLit q [124, 125, 126, 127, 128, 129, 130]) + (countLit q [131, 132, 133, 134, 135, 136, 137, 138]) := List.countP_append (p := literal q) (l₁ := [124, 125, 126, 127, 128, 129, 130]) (l₂ := [131, 132, 133, 134, 135, 136, 137, 138])
  have hm := merge_left (literal (valuationOf q) (257)) (literal (valuationOf q) (273)) (countLit q [124, 125, 126, 127, 128, 129, 130]) (countLit q [131, 132, 133, 134, 135, 136, 137, 138]) (count273 q) 1 (meaning257 q) (meaning273 q) hs
  change valuationOf q 257 = false ∨ valuationOf q 273 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause764 (q : Snake 81) (h : Conditions q) : valuation q 257 = false ∨ valuation q 273 = true := counterClause764 (baseVal q)

theorem counterClause765 (q : Nat → Bool) : valuationOf q 257 = false ∨ valuationOf q 271 = false ∨ valuationOf q 274 = true := by
  have hs : count273 q = (countLit q [124, 125, 126, 127, 128, 129, 130]) + (countLit q [131, 132, 133, 134, 135, 136, 137, 138]) := List.countP_append (p := literal q) (l₁ := [124, 125, 126, 127, 128, 129, 130]) (l₂ := [131, 132, 133, 134, 135, 136, 137, 138])
  have hm := merge_two (literal (valuationOf q) (257)) (literal (valuationOf q) (271)) (literal (valuationOf q) (274)) (countLit q [124, 125, 126, 127, 128, 129, 130]) (countLit q [131, 132, 133, 134, 135, 136, 137, 138]) (count273 q) 1 1 (meaning257 q) (meaning271 q) (meaning274 q) hs
  change valuationOf q 257 = false ∨ valuationOf q 271 = false ∨ valuationOf q 274 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause765 (q : Snake 81) (h : Conditions q) : valuation q 257 = false ∨ valuation q 271 = false ∨ valuation q 274 = true := counterClause765 (baseVal q)

theorem counterClause766 (q : Nat → Bool) : valuationOf q 258 = false ∨ valuationOf q 274 = true := by
  have hs : count273 q = (countLit q [124, 125, 126, 127, 128, 129, 130]) + (countLit q [131, 132, 133, 134, 135, 136, 137, 138]) := List.countP_append (p := literal q) (l₁ := [124, 125, 126, 127, 128, 129, 130]) (l₂ := [131, 132, 133, 134, 135, 136, 137, 138])
  have hm := merge_left (literal (valuationOf q) (258)) (literal (valuationOf q) (274)) (countLit q [124, 125, 126, 127, 128, 129, 130]) (countLit q [131, 132, 133, 134, 135, 136, 137, 138]) (count273 q) 2 (meaning258 q) (meaning274 q) hs
  change valuationOf q 258 = false ∨ valuationOf q 274 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause766 (q : Snake 81) (h : Conditions q) : valuation q 258 = false ∨ valuation q 274 = true := counterClause766 (baseVal q)

theorem counterClause767 (q : Nat → Bool) : valuationOf q 139 = false ∨ valuationOf q 277 = true := by
  have hs : count277 q = (countLit q [139]) + (countLit q [140, 141]) := List.countP_append (p := literal q) (l₁ := [139]) (l₂ := [140, 141])
  have hm := merge_left (literal (valuationOf q) (139)) (literal (valuationOf q) (277)) (countLit q [139]) (countLit q [140, 141]) (count277 q) 1 (meaning139 q) (meaning277 q) hs
  change valuationOf q 139 = false ∨ valuationOf q 277 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause767 (q : Snake 81) (h : Conditions q) : valuation q 139 = false ∨ valuation q 277 = true := counterClause767 (baseVal q)

theorem counterClause768 (q : Nat → Bool) : valuationOf q 142 = false ∨ valuationOf q 279 = true := by
  have hs : count279 q = (countLit q [142]) + (countLit q [144]) := List.countP_append (p := literal q) (l₁ := [142]) (l₂ := [144])
  have hm := merge_left (literal (valuationOf q) (142)) (literal (valuationOf q) (279)) (countLit q [142]) (countLit q [144]) (count279 q) 1 (meaning142 q) (meaning279 q) hs
  change valuationOf q 142 = false ∨ valuationOf q 279 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause768 (q : Snake 81) (h : Conditions q) : valuation q 142 = false ∨ valuation q 279 = true := counterClause768 (baseVal q)

theorem block23 (q : Snake 81) (h : Conditions q) : B112E097.Block23 (valuation q) :=
  ⟨clause737 q h, clause738 q h, clause739 q h, clause740 q h, clause741 q h, clause742 q h, clause743 q h, clause744 q h, clause745 q h, clause746 q h, clause747 q h, clause748 q h, clause749 q h, clause750 q h, clause751 q h, clause752 q h, clause753 q h, clause754 q h, clause755 q h, clause756 q h, clause757 q h, clause758 q h, clause759 q h, clause760 q h, clause761 q h, clause762 q h, clause763 q h, clause764 q h, clause765 q h, clause766 q h, clause767 q h, clause768 q h⟩

end
end Snake9.Regrowth.E112097
