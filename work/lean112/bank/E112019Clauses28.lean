import E112019Semantics
import B112E019Inputs
namespace Snake9.Regrowth.E112019
noncomputable section
local instance blockDec28 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause897 (q : Snake 81) (h : Conditions q) : valuation q 217 = false := by
  rw [value217]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (411 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause898 (q : Snake 81) (h : Conditions q) : valuation q 218 = false := by
  rw [value218]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (413 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause899 (q : Snake 81) (h : Conditions q) : valuation q 221 = false := by
  rw [value221]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (449 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause900 (q : Snake 81) (h : Conditions q) : valuation q 222 = false := by
  rw [value222]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (450 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause901 (q : Snake 81) (h : Conditions q) : valuation q 225 = false := by
  rw [value225]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (455 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause902 (q : Snake 81) (h : Conditions q) : valuation q 226 = false := by
  rw [value226]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (456 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause903 (q : Snake 81) (h : Conditions q) : valuation q 227 = false := by
  rw [value227]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (459 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause904 (q : Snake 81) (h : Conditions q) : valuation q 229 = false := by
  rw [value229]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (461 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause905 (q : Snake 81) (h : Conditions q) : valuation q 230 = false := by
  rw [value230]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (462 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause906 (q : Snake 81) (h : Conditions q) : valuation q 232 = false := by
  rw [value232]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (464 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause907 (q : Snake 81) (h : Conditions q) : valuation q 235 = false := by
  rw [value235]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (467 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause908 (q : Snake 81) (h : Conditions q) : valuation q 238 = false := by
  rw [value238]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (474 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause909 (q : Snake 81) (h : Conditions q) : valuation q 240 = false := by
  rw [value240]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (476 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause910 (q : Snake 81) (h : Conditions q) : valuation q 242 = false := by
  rw [value242]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (479 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem counterClause911 (q : Nat → Bool) : valuationOf q 123 = false ∨ valuationOf q 243 = true := by
  have hs : count243 q = (countLit q [123]) + (countLit q [124]) := List.countP_append (p := literal q) (l₁ := [123]) (l₂ := [124])
  have hm := merge_left (literal (valuationOf q) (123)) (literal (valuationOf q) (243)) (countLit q [123]) (countLit q [124]) (count243 q) 1 (meaning123 q) (meaning243 q) hs
  change valuationOf q 123 = false ∨ valuationOf q 243 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause911 (q : Snake 81) (h : Conditions q) : valuation q 123 = false ∨ valuation q 243 = true := counterClause911 (baseVal q)

theorem counterClause912 (q : Nat → Bool) : valuationOf q 243 = false ∨ valuationOf q 245 = true := by
  have hs : count245 q = (countLit q [122]) + (countLit q [123, 124]) := List.countP_append (p := literal q) (l₁ := [122]) (l₂ := [123, 124])
  have hm := merge_right (literal (valuationOf q) (243)) (literal (valuationOf q) (245)) (countLit q [122]) (countLit q [123, 124]) (count245 q) 1 (meaning243 q) (meaning245 q) hs
  change valuationOf q 243 = false ∨ valuationOf q 245 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause912 (q : Snake 81) (h : Conditions q) : valuation q 243 = false ∨ valuation q 245 = true := counterClause912 (baseVal q)

theorem counterClause913 (q : Nat → Bool) : valuationOf q 126 = false ∨ valuationOf q 247 = true := by
  have hs : count247 q = (countLit q [125]) + (countLit q [126]) := List.countP_append (p := literal q) (l₁ := [125]) (l₂ := [126])
  have hm := merge_right (literal (valuationOf q) (126)) (literal (valuationOf q) (247)) (countLit q [125]) (countLit q [126]) (count247 q) 1 (meaning126 q) (meaning247 q) hs
  change valuationOf q 126 = false ∨ valuationOf q 247 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause913 (q : Snake 81) (h : Conditions q) : valuation q 126 = false ∨ valuation q 247 = true := counterClause913 (baseVal q)

theorem counterClause914 (q : Nat → Bool) : valuationOf q 128 = false ∨ valuationOf q 249 = true := by
  have hs : count249 q = (countLit q [127]) + (countLit q [128]) := List.countP_append (p := literal q) (l₁ := [127]) (l₂ := [128])
  have hm := merge_right (literal (valuationOf q) (128)) (literal (valuationOf q) (249)) (countLit q [127]) (countLit q [128]) (count249 q) 1 (meaning128 q) (meaning249 q) hs
  change valuationOf q 128 = false ∨ valuationOf q 249 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause914 (q : Snake 81) (h : Conditions q) : valuation q 128 = false ∨ valuation q 249 = true := counterClause914 (baseVal q)

theorem counterClause915 (q : Nat → Bool) : valuationOf q 249 = false ∨ valuationOf q 251 = true := by
  have hs : count251 q = (countLit q [125, 126]) + (countLit q [127, 128]) := List.countP_append (p := literal q) (l₁ := [125, 126]) (l₂ := [127, 128])
  have hm := merge_right (literal (valuationOf q) (249)) (literal (valuationOf q) (251)) (countLit q [125, 126]) (countLit q [127, 128]) (count251 q) 1 (meaning249 q) (meaning251 q) hs
  change valuationOf q 249 = false ∨ valuationOf q 251 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause915 (q : Snake 81) (h : Conditions q) : valuation q 249 = false ∨ valuation q 251 = true := counterClause915 (baseVal q)

theorem counterClause916 (q : Nat → Bool) : valuationOf q 247 = false ∨ valuationOf q 251 = true := by
  have hs : count251 q = (countLit q [125, 126]) + (countLit q [127, 128]) := List.countP_append (p := literal q) (l₁ := [125, 126]) (l₂ := [127, 128])
  have hm := merge_left (literal (valuationOf q) (247)) (literal (valuationOf q) (251)) (countLit q [125, 126]) (countLit q [127, 128]) (count251 q) 1 (meaning247 q) (meaning251 q) hs
  change valuationOf q 247 = false ∨ valuationOf q 251 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause916 (q : Snake 81) (h : Conditions q) : valuation q 247 = false ∨ valuation q 251 = true := counterClause916 (baseVal q)

theorem counterClause917 (q : Nat → Bool) : valuationOf q 247 = false ∨ valuationOf q 249 = false ∨ valuationOf q 252 = true := by
  have hs : count251 q = (countLit q [125, 126]) + (countLit q [127, 128]) := List.countP_append (p := literal q) (l₁ := [125, 126]) (l₂ := [127, 128])
  have hm := merge_two (literal (valuationOf q) (247)) (literal (valuationOf q) (249)) (literal (valuationOf q) (252)) (countLit q [125, 126]) (countLit q [127, 128]) (count251 q) 1 1 (meaning247 q) (meaning249 q) (meaning252 q) hs
  change valuationOf q 247 = false ∨ valuationOf q 249 = false ∨ valuationOf q 252 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause917 (q : Snake 81) (h : Conditions q) : valuation q 247 = false ∨ valuation q 249 = false ∨ valuation q 252 = true := counterClause917 (baseVal q)

theorem counterClause918 (q : Nat → Bool) : valuationOf q 251 = false ∨ valuationOf q 253 = true := by
  have hs : count253 q = (countLit q [122, 123, 124]) + (countLit q [125, 126, 127, 128]) := List.countP_append (p := literal q) (l₁ := [122, 123, 124]) (l₂ := [125, 126, 127, 128])
  have hm := merge_right (literal (valuationOf q) (251)) (literal (valuationOf q) (253)) (countLit q [122, 123, 124]) (countLit q [125, 126, 127, 128]) (count253 q) 1 (meaning251 q) (meaning253 q) hs
  change valuationOf q 251 = false ∨ valuationOf q 253 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause918 (q : Snake 81) (h : Conditions q) : valuation q 251 = false ∨ valuation q 253 = true := counterClause918 (baseVal q)

theorem counterClause919 (q : Nat → Bool) : valuationOf q 252 = false ∨ valuationOf q 254 = true := by
  have hs : count253 q = (countLit q [122, 123, 124]) + (countLit q [125, 126, 127, 128]) := List.countP_append (p := literal q) (l₁ := [122, 123, 124]) (l₂ := [125, 126, 127, 128])
  have hm := merge_right (literal (valuationOf q) (252)) (literal (valuationOf q) (254)) (countLit q [122, 123, 124]) (countLit q [125, 126, 127, 128]) (count253 q) 2 (meaning252 q) (meaning254 q) hs
  change valuationOf q 252 = false ∨ valuationOf q 254 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause919 (q : Snake 81) (h : Conditions q) : valuation q 252 = false ∨ valuation q 254 = true := counterClause919 (baseVal q)

theorem counterClause920 (q : Nat → Bool) : valuationOf q 245 = false ∨ valuationOf q 253 = true := by
  have hs : count253 q = (countLit q [122, 123, 124]) + (countLit q [125, 126, 127, 128]) := List.countP_append (p := literal q) (l₁ := [122, 123, 124]) (l₂ := [125, 126, 127, 128])
  have hm := merge_left (literal (valuationOf q) (245)) (literal (valuationOf q) (253)) (countLit q [122, 123, 124]) (countLit q [125, 126, 127, 128]) (count253 q) 1 (meaning245 q) (meaning253 q) hs
  change valuationOf q 245 = false ∨ valuationOf q 253 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause920 (q : Snake 81) (h : Conditions q) : valuation q 245 = false ∨ valuation q 253 = true := counterClause920 (baseVal q)

theorem counterClause921 (q : Nat → Bool) : valuationOf q 130 = false ∨ valuationOf q 255 = true := by
  have hs : count255 q = (countLit q [129]) + (countLit q [130]) := List.countP_append (p := literal q) (l₁ := [129]) (l₂ := [130])
  have hm := merge_right (literal (valuationOf q) (130)) (literal (valuationOf q) (255)) (countLit q [129]) (countLit q [130]) (count255 q) 1 (meaning130 q) (meaning255 q) hs
  change valuationOf q 130 = false ∨ valuationOf q 255 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause921 (q : Snake 81) (h : Conditions q) : valuation q 130 = false ∨ valuation q 255 = true := counterClause921 (baseVal q)

theorem counterClause922 (q : Nat → Bool) : valuationOf q 132 = false ∨ valuationOf q 257 = true := by
  have hs : count257 q = (countLit q [131]) + (countLit q [132]) := List.countP_append (p := literal q) (l₁ := [131]) (l₂ := [132])
  have hm := merge_right (literal (valuationOf q) (132)) (literal (valuationOf q) (257)) (countLit q [131]) (countLit q [132]) (count257 q) 1 (meaning132 q) (meaning257 q) hs
  change valuationOf q 132 = false ∨ valuationOf q 257 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause922 (q : Snake 81) (h : Conditions q) : valuation q 132 = false ∨ valuation q 257 = true := counterClause922 (baseVal q)

theorem counterClause923 (q : Nat → Bool) : valuationOf q 257 = false ∨ valuationOf q 259 = true := by
  have hs : count259 q = (countLit q [129, 130]) + (countLit q [131, 132]) := List.countP_append (p := literal q) (l₁ := [129, 130]) (l₂ := [131, 132])
  have hm := merge_right (literal (valuationOf q) (257)) (literal (valuationOf q) (259)) (countLit q [129, 130]) (countLit q [131, 132]) (count259 q) 1 (meaning257 q) (meaning259 q) hs
  change valuationOf q 257 = false ∨ valuationOf q 259 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause923 (q : Snake 81) (h : Conditions q) : valuation q 257 = false ∨ valuation q 259 = true := counterClause923 (baseVal q)

theorem counterClause924 (q : Nat → Bool) : valuationOf q 255 = false ∨ valuationOf q 259 = true := by
  have hs : count259 q = (countLit q [129, 130]) + (countLit q [131, 132]) := List.countP_append (p := literal q) (l₁ := [129, 130]) (l₂ := [131, 132])
  have hm := merge_left (literal (valuationOf q) (255)) (literal (valuationOf q) (259)) (countLit q [129, 130]) (countLit q [131, 132]) (count259 q) 1 (meaning255 q) (meaning259 q) hs
  change valuationOf q 255 = false ∨ valuationOf q 259 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause924 (q : Snake 81) (h : Conditions q) : valuation q 255 = false ∨ valuation q 259 = true := counterClause924 (baseVal q)

theorem counterClause925 (q : Nat → Bool) : valuationOf q 135 = false ∨ valuationOf q 263 = true := by
  have hs : count263 q = (countLit q [135]) + (countLit q [136]) := List.countP_append (p := literal q) (l₁ := [135]) (l₂ := [136])
  have hm := merge_left (literal (valuationOf q) (135)) (literal (valuationOf q) (263)) (countLit q [135]) (countLit q [136]) (count263 q) 1 (meaning135 q) (meaning263 q) hs
  change valuationOf q 135 = false ∨ valuationOf q 263 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause925 (q : Snake 81) (h : Conditions q) : valuation q 135 = false ∨ valuation q 263 = true := counterClause925 (baseVal q)

theorem counterClause926 (q : Nat → Bool) : valuationOf q 263 = false ∨ valuationOf q 265 = true := by
  have hs : count265 q = (countLit q [133, 134]) + (countLit q [135, 136]) := List.countP_append (p := literal q) (l₁ := [133, 134]) (l₂ := [135, 136])
  have hm := merge_right (literal (valuationOf q) (263)) (literal (valuationOf q) (265)) (countLit q [133, 134]) (countLit q [135, 136]) (count265 q) 1 (meaning263 q) (meaning265 q) hs
  change valuationOf q 263 = false ∨ valuationOf q 265 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause926 (q : Snake 81) (h : Conditions q) : valuation q 263 = false ∨ valuation q 265 = true := counterClause926 (baseVal q)

theorem counterClause927 (q : Nat → Bool) : valuationOf q 265 = false ∨ valuationOf q 267 = true := by
  have hs : count267 q = (countLit q [129, 130, 131, 132]) + (countLit q [133, 134, 135, 136]) := List.countP_append (p := literal q) (l₁ := [129, 130, 131, 132]) (l₂ := [133, 134, 135, 136])
  have hm := merge_right (literal (valuationOf q) (265)) (literal (valuationOf q) (267)) (countLit q [129, 130, 131, 132]) (countLit q [133, 134, 135, 136]) (count267 q) 1 (meaning265 q) (meaning267 q) hs
  change valuationOf q 265 = false ∨ valuationOf q 267 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause927 (q : Snake 81) (h : Conditions q) : valuation q 265 = false ∨ valuation q 267 = true := counterClause927 (baseVal q)

theorem counterClause928 (q : Nat → Bool) : valuationOf q 259 = false ∨ valuationOf q 267 = true := by
  have hs : count267 q = (countLit q [129, 130, 131, 132]) + (countLit q [133, 134, 135, 136]) := List.countP_append (p := literal q) (l₁ := [129, 130, 131, 132]) (l₂ := [133, 134, 135, 136])
  have hm := merge_left (literal (valuationOf q) (259)) (literal (valuationOf q) (267)) (countLit q [129, 130, 131, 132]) (countLit q [133, 134, 135, 136]) (count267 q) 1 (meaning259 q) (meaning267 q) hs
  change valuationOf q 259 = false ∨ valuationOf q 267 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause928 (q : Snake 81) (h : Conditions q) : valuation q 259 = false ∨ valuation q 267 = true := counterClause928 (baseVal q)

theorem block28 (q : Snake 81) (h : Conditions q) : B112E019.Block28 (valuation q) :=
  ⟨clause897 q h, clause898 q h, clause899 q h, clause900 q h, clause901 q h, clause902 q h, clause903 q h, clause904 q h, clause905 q h, clause906 q h, clause907 q h, clause908 q h, clause909 q h, clause910 q h, clause911 q h, clause912 q h, clause913 q h, clause914 q h, clause915 q h, clause916 q h, clause917 q h, clause918 q h, clause919 q h, clause920 q h, clause921 q h, clause922 q h, clause923 q h, clause924 q h, clause925 q h, clause926 q h, clause927 q h, clause928 q h⟩

end
end Snake9.Regrowth.E112019
