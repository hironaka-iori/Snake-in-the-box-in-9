import E112040Semantics
import B112E040Inputs
namespace Snake9.Regrowth.E112040
noncomputable section
local instance blockDec22 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause705 (q : Snake 81) (h : Conditions q) : valuation q 202 = false := by
  rw [value202]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (301 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause706 (q : Snake 81) (h : Conditions q) : valuation q 207 = false := by
  rw [value207]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (310 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause707 (q : Snake 81) (h : Conditions q) : valuation q 208 = false := by
  rw [value208]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (314 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause708 (q : Snake 81) (h : Conditions q) : valuation q 210 = false := by
  rw [value210]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (316 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause709 (q : Snake 81) (h : Conditions q) : valuation q 212 = false := by
  rw [value212]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (352 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause710 (q : Snake 81) (h : Conditions q) : valuation q 214 = false := by
  rw [value214]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (357 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause711 (q : Snake 81) (h : Conditions q) : valuation q 215 = false := by
  rw [value215]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (358 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause712 (q : Snake 81) (h : Conditions q) : valuation q 218 = false := by
  rw [value218]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (361 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause713 (q : Snake 81) (h : Conditions q) : valuation q 219 = false := by
  rw [value219]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (362 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause714 (q : Snake 81) (h : Conditions q) : valuation q 225 = false := by
  rw [value225]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (375 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause715 (q : Snake 81) (h : Conditions q) : valuation q 226 = false := by
  rw [value226]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (376 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause716 (q : Snake 81) (h : Conditions q) : valuation q 229 = false := by
  rw [value229]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (379 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause717 (q : Snake 81) (h : Conditions q) : valuation q 230 = false := by
  rw [value230]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (381 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause718 (q : Snake 81) (h : Conditions q) : valuation q 231 = false := by
  rw [value231]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (382 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause719 (q : Snake 81) (h : Conditions q) : valuation q 233 = false := by
  rw [value233]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (425 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause720 (q : Snake 81) (h : Conditions q) : valuation q 235 = false := by
  rw [value235]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (440 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause721 (q : Snake 81) (h : Conditions q) : valuation q 236 = false := by
  rw [value236]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (443 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause722 (q : Snake 81) (h : Conditions q) : valuation q 240 = false := by
  rw [value240]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (511 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem counterClause723 (q : Nat → Bool) : valuationOf q 122 = false ∨ valuationOf q 241 = true := by
  have hs : count241 q = (countLit q [122]) + (countLit q [123]) := List.countP_append (p := literal q) (l₁ := [122]) (l₂ := [123])
  have hm := merge_left (literal (valuationOf q) (122)) (literal (valuationOf q) (241)) (countLit q [122]) (countLit q [123]) (count241 q) 1 (meaning122 q) (meaning241 q) hs
  change valuationOf q 122 = false ∨ valuationOf q 241 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause723 (q : Snake 81) (h : Conditions q) : valuation q 122 = false ∨ valuation q 241 = true := counterClause723 (baseVal q)

theorem counterClause724 (q : Nat → Bool) : valuationOf q 241 = false ∨ valuationOf q 243 = true := by
  have hs : count243 q = (countLit q [121]) + (countLit q [122, 123]) := List.countP_append (p := literal q) (l₁ := [121]) (l₂ := [122, 123])
  have hm := merge_right (literal (valuationOf q) (241)) (literal (valuationOf q) (243)) (countLit q [121]) (countLit q [122, 123]) (count243 q) 1 (meaning241 q) (meaning243 q) hs
  change valuationOf q 241 = false ∨ valuationOf q 243 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause724 (q : Snake 81) (h : Conditions q) : valuation q 241 = false ∨ valuation q 243 = true := counterClause724 (baseVal q)

theorem counterClause725 (q : Nat → Bool) : valuationOf q 125 = false ∨ valuationOf q 245 = true := by
  have hs : count245 q = (countLit q [124]) + (countLit q [125]) := List.countP_append (p := literal q) (l₁ := [124]) (l₂ := [125])
  have hm := merge_right (literal (valuationOf q) (125)) (literal (valuationOf q) (245)) (countLit q [124]) (countLit q [125]) (count245 q) 1 (meaning125 q) (meaning245 q) hs
  change valuationOf q 125 = false ∨ valuationOf q 245 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause725 (q : Snake 81) (h : Conditions q) : valuation q 125 = false ∨ valuation q 245 = true := counterClause725 (baseVal q)

theorem counterClause726 (q : Nat → Bool) : valuationOf q 245 = false ∨ valuationOf q 249 = true := by
  have hs : count249 q = (countLit q [124, 125]) + (countLit q [126, 127]) := List.countP_append (p := literal q) (l₁ := [124, 125]) (l₂ := [126, 127])
  have hm := merge_left (literal (valuationOf q) (245)) (literal (valuationOf q) (249)) (countLit q [124, 125]) (countLit q [126, 127]) (count249 q) 1 (meaning245 q) (meaning249 q) hs
  change valuationOf q 245 = false ∨ valuationOf q 249 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause726 (q : Snake 81) (h : Conditions q) : valuation q 245 = false ∨ valuation q 249 = true := counterClause726 (baseVal q)

theorem counterClause727 (q : Nat → Bool) : valuationOf q 249 = false ∨ valuationOf q 251 = true := by
  have hs : count251 q = (countLit q [121, 122, 123]) + (countLit q [124, 125, 126, 127]) := List.countP_append (p := literal q) (l₁ := [121, 122, 123]) (l₂ := [124, 125, 126, 127])
  have hm := merge_right (literal (valuationOf q) (249)) (literal (valuationOf q) (251)) (countLit q [121, 122, 123]) (countLit q [124, 125, 126, 127]) (count251 q) 1 (meaning249 q) (meaning251 q) hs
  change valuationOf q 249 = false ∨ valuationOf q 251 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause727 (q : Snake 81) (h : Conditions q) : valuation q 249 = false ∨ valuation q 251 = true := counterClause727 (baseVal q)

theorem counterClause728 (q : Nat → Bool) : valuationOf q 243 = false ∨ valuationOf q 251 = true := by
  have hs : count251 q = (countLit q [121, 122, 123]) + (countLit q [124, 125, 126, 127]) := List.countP_append (p := literal q) (l₁ := [121, 122, 123]) (l₂ := [124, 125, 126, 127])
  have hm := merge_left (literal (valuationOf q) (243)) (literal (valuationOf q) (251)) (countLit q [121, 122, 123]) (countLit q [124, 125, 126, 127]) (count251 q) 1 (meaning243 q) (meaning251 q) hs
  change valuationOf q 243 = false ∨ valuationOf q 251 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause728 (q : Snake 81) (h : Conditions q) : valuation q 243 = false ∨ valuation q 251 = true := counterClause728 (baseVal q)

theorem counterClause729 (q : Nat → Bool) : valuationOf q 128 = false ∨ valuationOf q 255 = true := by
  have hs : count255 q = (countLit q [128]) + (countLit q [129, 130]) := List.countP_append (p := literal q) (l₁ := [128]) (l₂ := [129, 130])
  have hm := merge_left (literal (valuationOf q) (128)) (literal (valuationOf q) (255)) (countLit q [128]) (countLit q [129, 130]) (count255 q) 1 (meaning128 q) (meaning255 q) hs
  change valuationOf q 128 = false ∨ valuationOf q 255 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause729 (q : Snake 81) (h : Conditions q) : valuation q 128 = false ∨ valuation q 255 = true := counterClause729 (baseVal q)

theorem counterClause730 (q : Nat → Bool) : valuationOf q 131 = false ∨ valuationOf q 257 = true := by
  have hs : count257 q = (countLit q [131]) + (countLit q [132]) := List.countP_append (p := literal q) (l₁ := [131]) (l₂ := [132])
  have hm := merge_left (literal (valuationOf q) (131)) (literal (valuationOf q) (257)) (countLit q [131]) (countLit q [132]) (count257 q) 1 (meaning131 q) (meaning257 q) hs
  change valuationOf q 131 = false ∨ valuationOf q 257 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause730 (q : Snake 81) (h : Conditions q) : valuation q 131 = false ∨ valuation q 257 = true := counterClause730 (baseVal q)

theorem counterClause731 (q : Nat → Bool) : valuationOf q 134 = false ∨ valuationOf q 259 = true := by
  have hs : count259 q = (countLit q [133]) + (countLit q [134]) := List.countP_append (p := literal q) (l₁ := [133]) (l₂ := [134])
  have hm := merge_right (literal (valuationOf q) (134)) (literal (valuationOf q) (259)) (countLit q [133]) (countLit q [134]) (count259 q) 1 (meaning134 q) (meaning259 q) hs
  change valuationOf q 134 = false ∨ valuationOf q 259 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause731 (q : Snake 81) (h : Conditions q) : valuation q 134 = false ∨ valuation q 259 = true := counterClause731 (baseVal q)

theorem counterClause732 (q : Nat → Bool) : valuationOf q 259 = false ∨ valuationOf q 261 = true := by
  have hs : count261 q = (countLit q [131, 132]) + (countLit q [133, 134]) := List.countP_append (p := literal q) (l₁ := [131, 132]) (l₂ := [133, 134])
  have hm := merge_right (literal (valuationOf q) (259)) (literal (valuationOf q) (261)) (countLit q [131, 132]) (countLit q [133, 134]) (count261 q) 1 (meaning259 q) (meaning261 q) hs
  change valuationOf q 259 = false ∨ valuationOf q 261 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause732 (q : Snake 81) (h : Conditions q) : valuation q 259 = false ∨ valuation q 261 = true := counterClause732 (baseVal q)

theorem counterClause733 (q : Nat → Bool) : valuationOf q 257 = false ∨ valuationOf q 261 = true := by
  have hs : count261 q = (countLit q [131, 132]) + (countLit q [133, 134]) := List.countP_append (p := literal q) (l₁ := [131, 132]) (l₂ := [133, 134])
  have hm := merge_left (literal (valuationOf q) (257)) (literal (valuationOf q) (261)) (countLit q [131, 132]) (countLit q [133, 134]) (count261 q) 1 (meaning257 q) (meaning261 q) hs
  change valuationOf q 257 = false ∨ valuationOf q 261 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause733 (q : Snake 81) (h : Conditions q) : valuation q 257 = false ∨ valuation q 261 = true := counterClause733 (baseVal q)

theorem counterClause734 (q : Nat → Bool) : valuationOf q 257 = false ∨ valuationOf q 259 = false ∨ valuationOf q 262 = true := by
  have hs : count261 q = (countLit q [131, 132]) + (countLit q [133, 134]) := List.countP_append (p := literal q) (l₁ := [131, 132]) (l₂ := [133, 134])
  have hm := merge_two (literal (valuationOf q) (257)) (literal (valuationOf q) (259)) (literal (valuationOf q) (262)) (countLit q [131, 132]) (countLit q [133, 134]) (count261 q) 1 1 (meaning257 q) (meaning259 q) (meaning262 q) hs
  change valuationOf q 257 = false ∨ valuationOf q 259 = false ∨ valuationOf q 262 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause734 (q : Snake 81) (h : Conditions q) : valuation q 257 = false ∨ valuation q 259 = false ∨ valuation q 262 = true := counterClause734 (baseVal q)

theorem counterClause735 (q : Nat → Bool) : valuationOf q 261 = false ∨ valuationOf q 263 = true := by
  have hs : count263 q = (countLit q [128, 129, 130]) + (countLit q [131, 132, 133, 134]) := List.countP_append (p := literal q) (l₁ := [128, 129, 130]) (l₂ := [131, 132, 133, 134])
  have hm := merge_right (literal (valuationOf q) (261)) (literal (valuationOf q) (263)) (countLit q [128, 129, 130]) (countLit q [131, 132, 133, 134]) (count263 q) 1 (meaning261 q) (meaning263 q) hs
  change valuationOf q 261 = false ∨ valuationOf q 263 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause735 (q : Snake 81) (h : Conditions q) : valuation q 261 = false ∨ valuation q 263 = true := counterClause735 (baseVal q)

theorem counterClause736 (q : Nat → Bool) : valuationOf q 262 = false ∨ valuationOf q 264 = true := by
  have hs : count263 q = (countLit q [128, 129, 130]) + (countLit q [131, 132, 133, 134]) := List.countP_append (p := literal q) (l₁ := [128, 129, 130]) (l₂ := [131, 132, 133, 134])
  have hm := merge_right (literal (valuationOf q) (262)) (literal (valuationOf q) (264)) (countLit q [128, 129, 130]) (countLit q [131, 132, 133, 134]) (count263 q) 2 (meaning262 q) (meaning264 q) hs
  change valuationOf q 262 = false ∨ valuationOf q 264 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause736 (q : Snake 81) (h : Conditions q) : valuation q 262 = false ∨ valuation q 264 = true := counterClause736 (baseVal q)

theorem block22 (q : Snake 81) (h : Conditions q) : B112E040.Block22 (valuation q) :=
  ⟨clause705 q h, clause706 q h, clause707 q h, clause708 q h, clause709 q h, clause710 q h, clause711 q h, clause712 q h, clause713 q h, clause714 q h, clause715 q h, clause716 q h, clause717 q h, clause718 q h, clause719 q h, clause720 q h, clause721 q h, clause722 q h, clause723 q h, clause724 q h, clause725 q h, clause726 q h, clause727 q h, clause728 q h, clause729 q h, clause730 q h, clause731 q h, clause732 q h, clause733 q h, clause734 q h, clause735 q h, clause736 q h⟩

end
end Snake9.Regrowth.E112040
